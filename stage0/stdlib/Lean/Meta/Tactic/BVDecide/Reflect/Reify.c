// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.Reify
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Basic import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedLemmas import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical import Lean.Meta.Sym.LitValues import Lean.Meta.AppBuilder import Std.Tactic.BVDecide.Reflect import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.Simp.CongrInfo
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_getCongrInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 35, 113, 77, 117, 41, 40, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.BVDecide.Reflect.Reify"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 109, .m_capacity = 109, .m_length = 108, .m_data = "_private.Lean.Meta.Tactic.BVDecide.Reflect.Reify.0.Lean.Meta.Tactic.BVDecide.checkFunAtom.getFunctionPattern"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "assertion violation: args.size == mask.size\n      "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__3;
static const lean_array_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__2_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__5_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Registered fun atom: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__7_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__8;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", mask: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__9 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__9_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__10;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Checking for fun atom "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_checkTheoryAtom(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_checkTheoryAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30_spec__31___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "extract_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "replicate_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "append_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofBool_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_shiftRight___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 40, 162, 224, 189, 205, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "clz"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 156, 207, 111, 211, 81, 174, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reverse"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(244, 136, 165, 42, 211, 46, 208, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 30, 240, 114, 51, 110, 152, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 181, 93, 155, 164, 43, 234, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(234, 123, 74, 120, 175, 214, 39, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sshiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(206, 65, 29, 246, 207, 155, 165, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "complement"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Complement"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(6, 52, 244, 64, 3, 58, 115, 79)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(168, 254, 142, 44, 189, 175, 152, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLsb'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(47, 201, 218, 12, 248, 124, 75, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sshiftRight'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(69, 78, 17, 52, 147, 31, 186, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "shiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVExpr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(71, 199, 243, 56, 253, 18, 242, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shiftRight_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value),LEAN_SCALAR_PTR_LITERAL(216, 161, 38, 33, 237, 165, 100, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 209, 242, 75, 214, 61, 180, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "shiftLeft_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 67, 4, 228, 88, 122, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hAppend"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HAppend"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value),LEAN_SCALAR_PTR_LITERAL(137, 35, 233, 160, 196, 216, 250, 31)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value),LEAN_SCALAR_PTR_LITERAL(181, 97, 51, 176, 35, 131, 5, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value),LEAN_SCALAR_PTR_LITERAL(20, 152, 116, 121, 198, 45, 139, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 182, 211, 92, 78, 225, 70, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVBinOp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 193, 54, 191, 172, 208, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 33, 141, 132, 156, 154, 79, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(68, 221, 44, 95, 169, 9, 73, 176)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(236, 85, 182, 141, 252, 28, 21, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(66, 46, 226, 27, 15, 162, 209, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "udiv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(97, 106, 189, 172, 252, 249, 116, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "umod"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value),LEAN_SCALAR_PTR_LITERAL(185, 164, 216, 8, 44, 82, 23, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "xor_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 197, 38, 228, 52, 44, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_value),LEAN_SCALAR_PTR_LITERAL(177, 5, 60, 46, 78, 68, 243, 177)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value),LEAN_SCALAR_PTR_LITERAL(221, 159, 178, 23, 57, 108, 69, 225)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "udiv_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value),LEAN_SCALAR_PTR_LITERAL(118, 153, 195, 105, 228, 227, 83, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "umod_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value),LEAN_SCALAR_PTR_LITERAL(102, 27, 81, 101, 187, 174, 242, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "internal error: constant shift should have been eliminated."};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value),LEAN_SCALAR_PTR_LITERAL(148, 222, 207, 10, 98, 174, 247, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "arithShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value),LEAN_SCALAR_PTR_LITERAL(103, 53, 88, 127, 221, 158, 175, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "arithShiftRight_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value),LEAN_SCALAR_PTR_LITERAL(52, 31, 162, 102, 135, 66, 0, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extract"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value),LEAN_SCALAR_PTR_LITERAL(13, 22, 63, 119, 146, 191, 248, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 7, 174, 153, 9, 234, 93, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__2;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___lam__0___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value_aux_0),((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value_aux_0),((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 226, 96, 197, 228, 245, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ult"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 62, 117, 244, 108, 14, 8, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 227, 220, 143, 67, 138, 133, 64)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value),LEAN_SCALAR_PTR_LITERAL(189, 30, 154, 245, 30, 224, 55, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "un"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(42, 186, 200, 92, 180, 128, 216, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVUnOp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 170, 248, 163, 146, 14, 228, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 116, 55, 155, 243, 43, 27, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(112, 197, 123, 204, 93, 250, 252, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "arithShiftRightConst"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(88, 95, 189, 240, 90, 71, 117, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(84, 226, 239, 81, 45, 17, 252, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(221, 66, 219, 130, 52, 97, 84, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(214, 119, 73, 246, 51, 241, 221, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "arithShiftRightNat_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value),LEAN_SCALAR_PTR_LITERAL(59, 32, 240, 3, 69, 217, 10, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(105, 148, 101, 98, 245, 160, 38, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "rotateLeft_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value),LEAN_SCALAR_PTR_LITERAL(32, 228, 194, 198, 195, 74, 36, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "rotateRight_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value),LEAN_SCALAR_PTR_LITERAL(61, 145, 127, 186, 176, 174, 37, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reverse_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value),LEAN_SCALAR_PTR_LITERAL(182, 175, 240, 129, 220, 112, 73, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "clz_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value),LEAN_SCALAR_PTR_LITERAL(108, 254, 78, 195, 105, 118, 43, 132)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cpop_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value),LEAN_SCALAR_PTR_LITERAL(181, 75, 188, 170, 67, 231, 89, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30_spec__31(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg(lean_object* v_e_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_Sym_inferType(v_e_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v___x_15_, 1);
v___x_17_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_16_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_32_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_32_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_32_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_32_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = l_Lean_Expr_cleanupAnnotations(v_a_18_);
v___x_23_ = l_Lean_Expr_isApp(v___x_22_);
if (v___x_23_ == 0)
{
lean_dec_ref(v___x_22_);
lean_del_object(v___x_20_);
goto v___jp_12_;
}
else
{
lean_object* v_arg_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v_arg_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc_ref(v_arg_24_);
v___x_25_ = l_Lean_Expr_appFnCleanup___redArg(v___x_22_);
v___x_26_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1));
v___x_27_ = l_Lean_Expr_isConstOf(v___x_25_, v___x_26_);
lean_dec_ref(v___x_25_);
if (v___x_27_ == 0)
{
lean_dec_ref(v_arg_24_);
lean_del_object(v___x_20_);
goto v___jp_12_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_28_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_24_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_28_);
v___x_30_ = v___x_20_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
else
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
v_a_33_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v___x_17_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_17_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_a_41_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_15_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_15_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
v___jp_12_:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___boxed(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg(v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom(lean_object* v_e_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg(v_e_58_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___boxed(lean_object* v_e_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom(v_e_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg(lean_object* v_e_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Sym_inferType(v_e_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_108_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_108_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_108_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_108_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_102_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__1));
v___x_103_ = l_Lean_Expr_isConstOf(v_a_98_, v___x_102_);
lean_dec(v_a_98_);
v___x_104_ = lean_box(v___x_103_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_104_);
v___x_106_ = v___x_100_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_97_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_97_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___boxed(lean_object* v_e_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg(v_e_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom(lean_object* v_e_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg(v_e_126_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___boxed(lean_object* v_e_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom(v_e_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___redArg(lean_object* v_fn_154_, lean_object* v_args_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Meta_Sym_getCongrInfo___redArg(v_fn_154_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_208_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_208_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_208_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_208_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
switch(lean_obj_tag(v_a_163_))
{
case 1:
{
lean_object* v_prefixSize_167_; lean_object* v_suffixSize_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v_prefixSize_167_ = lean_ctor_get(v_a_163_, 0);
lean_inc_n(v_prefixSize_167_, 2);
v_suffixSize_168_ = lean_ctor_get(v_a_163_, 1);
lean_inc_n(v_suffixSize_168_, 2);
lean_dec_ref_known(v_a_163_, 2);
v___x_169_ = 0;
v___x_170_ = lean_box(v___x_169_);
v___x_171_ = lean_mk_array(v_prefixSize_167_, v___x_170_);
v___x_172_ = 1;
v___x_173_ = lean_box(v___x_172_);
v___x_174_ = lean_mk_array(v_suffixSize_168_, v___x_173_);
v___x_175_ = l_Array_append___redArg(v___x_171_, v___x_174_);
lean_dec_ref(v___x_174_);
v___x_176_ = lean_array_get_size(v_args_155_);
v___x_177_ = lean_nat_sub(v___x_176_, v_suffixSize_168_);
lean_dec(v_suffixSize_168_);
v___x_178_ = lean_nat_sub(v___x_177_, v_prefixSize_167_);
lean_dec(v_prefixSize_167_);
lean_dec(v___x_177_);
v___x_179_ = lean_box(v___x_169_);
v___x_180_ = lean_mk_array(v___x_178_, v___x_179_);
v___x_181_ = l_Array_append___redArg(v___x_175_, v___x_180_);
lean_dec_ref(v___x_180_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_182_);
v___x_184_ = v___x_165_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
case 2:
{
lean_object* v_rewritable_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_203_; 
v_rewritable_186_ = lean_ctor_get(v_a_163_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_a_163_);
if (v_isSharedCheck_203_ == 0)
{
v___x_188_ = v_a_163_;
v_isShared_189_ = v_isSharedCheck_203_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_rewritable_186_);
lean_dec(v_a_163_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_203_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_190_ = lean_array_get_size(v_args_155_);
v___x_191_ = lean_array_get_size(v_rewritable_186_);
v___x_192_ = lean_nat_sub(v___x_190_, v___x_191_);
v___x_193_ = 0;
v___x_194_ = lean_box(v___x_193_);
v___x_195_ = lean_mk_array(v___x_192_, v___x_194_);
v___x_196_ = l_Array_append___redArg(v_rewritable_186_, v___x_195_);
lean_dec_ref(v___x_195_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
lean_ctor_set(v___x_188_, 0, v___x_196_);
v___x_198_ = v___x_188_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_198_);
v___x_200_ = v___x_165_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
default: 
{
lean_object* v___x_204_; lean_object* v___x_206_; 
lean_dec(v_a_163_);
v___x_204_ = lean_box(0);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_204_);
v___x_206_ = v___x_165_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_162_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_162_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___redArg___boxed(lean_object* v_fn_217_, lean_object* v_args_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___redArg(v_fn_217_, v_args_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_args_218_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask(lean_object* v_fn_226_, lean_object* v_args_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___redArg(v_fn_226_, v_args_227_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___boxed(lean_object* v_fn_236_, lean_object* v_args_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask(v_fn_236_, v_args_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_args_237_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg(lean_object* v_e_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_258_; 
lean_inc_ref(v_e_250_);
v___x_258_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_250_, v_a_251_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_274_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_274_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_274_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_274_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = l_Lean_Expr_cleanupAnnotations(v_a_259_);
v___x_264_ = l_Lean_Expr_isApp(v___x_263_);
if (v___x_264_ == 0)
{
lean_dec_ref(v___x_263_);
lean_del_object(v___x_261_);
goto v___jp_253_;
}
else
{
lean_object* v_arg_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_arg_265_ = lean_ctor_get(v___x_263_, 1);
lean_inc_ref(v_arg_265_);
v___x_266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_263_);
v___x_267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___closed__1));
v___x_268_ = l_Lean_Expr_isConstOf(v___x_266_, v___x_267_);
lean_dec_ref(v___x_266_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_arg_265_);
lean_del_object(v___x_261_);
goto v___jp_253_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec_ref(v_e_250_);
v___x_269_ = lean_box(v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v_arg_265_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_270_);
v___x_272_ = v___x_261_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_e_250_);
v_a_275_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_258_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_258_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
v___jp_253_:
{
uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = 0;
v___x_255_ = lean_box(v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_e_250_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg___boxed(lean_object* v_e_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg(v_e_283_, v_a_284_);
lean_dec(v_a_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom(lean_object* v_e_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg(v_e_287_, v_a_291_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___boxed(lean_object* v_e_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom(v_e_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
return v_res_304_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___closed__0(void){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Sym_instInhabitedSymM___redArg();
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0(lean_object* v_msg_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_3063__overap_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___closed__0);
v___x_3063__overap_315_ = lean_panic_fn_borrowed(v___x_314_, v_msg_306_);
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
v___x_316_ = lean_apply_7(v___x_3063__overap_315_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, lean_box(0));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0___boxed(lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___lam__0(lean_object* v_snd_326_, lean_object* v_x_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v_snd_326_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___lam__0___boxed(lean_object* v_snd_336_, lean_object* v_x_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___lam__0(v_snd_336_, v_x_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec_ref(v_x_337_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3(size_t v_sz_346_, size_t v_i_347_, lean_object* v_bs_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_usize_dec_lt(v_i_347_, v_sz_346_);
if (v___x_349_ == 0)
{
return v_bs_348_;
}
else
{
lean_object* v_v_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_366_; 
v_v_350_ = lean_array_uget(v_bs_348_, v_i_347_);
v_fst_351_ = lean_ctor_get(v_v_350_, 0);
v_snd_352_ = lean_ctor_get(v_v_350_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_v_350_);
if (v_isSharedCheck_366_ == 0)
{
v___x_354_ = v_v_350_;
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_snd_352_);
lean_inc(v_fst_351_);
lean_dec(v_v_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v_bs_x27_357_; lean_object* v___f_358_; lean_object* v___x_360_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v_bs_x27_357_ = lean_array_uset(v_bs_348_, v_i_347_, v___x_356_);
v___f_358_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___lam__0___boxed), 9, 1);
lean_closure_set(v___f_358_, 0, v_snd_352_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___f_358_);
v___x_360_ = v___x_354_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___f_358_);
v___x_360_ = v_reuseFailAlloc_365_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_347_, v___x_361_);
v___x_363_ = lean_array_uset(v_bs_x27_357_, v_i_347_, v___x_360_);
v_i_347_ = v___x_362_;
v_bs_348_ = v___x_363_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3___boxed(lean_object* v_sz_367_, lean_object* v_i_368_, lean_object* v_bs_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_367_);
lean_dec(v_sz_367_);
v_i_boxed_371_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3(v_sz_boxed_370_, v_i_boxed_371_, v_bs_369_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___lam__0(lean_object* v_k_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v_b_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
lean_inc(v___y_380_);
lean_inc_ref(v___y_379_);
lean_inc(v___y_378_);
lean_inc_ref(v___y_377_);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
v___x_382_ = lean_apply_8(v_k_373_, v_b_376_, v___y_374_, v___y_375_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, lean_box(0));
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___lam__0___boxed(lean_object* v_k_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___lam__0(v_k_383_, v___y_384_, v___y_385_, v_b_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_name_393_, uint8_t v_bi_394_, lean_object* v_type_395_, lean_object* v_k_396_, uint8_t v_kind_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_406_; 
lean_inc(v___y_399_);
lean_inc_ref(v___y_398_);
v___f_405_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_405_, 0, v_k_396_);
lean_closure_set(v___f_405_, 1, v___y_398_);
lean_closure_set(v___f_405_, 2, v___y_399_);
v___x_406_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_393_, v_bi_394_, v_type_395_, v___f_405_, v_kind_397_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_406_) == 0)
{
return v___x_406_;
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_name_415_, lean_object* v_bi_416_, lean_object* v_type_417_, lean_object* v_k_418_, lean_object* v_kind_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v_bi_boxed_427_; uint8_t v_kind_boxed_428_; lean_object* v_res_429_; 
v_bi_boxed_427_ = lean_unbox(v_bi_416_);
v_kind_boxed_428_ = lean_unbox(v_kind_419_);
v_res_429_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg(v_name_415_, v_bi_boxed_427_, v_type_417_, v_k_418_, v_kind_boxed_428_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__0(lean_object* v___x_430_, lean_object* v___x_431_, lean_object* v_a_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_6201__overap_440_; lean_object* v___x_441_; 
v___x_6201__overap_440_ = l_instInhabitedOfMonad___redArg(v___x_430_, v___x_431_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
v___x_441_ = lean_apply_7(v___x_6201__overap_440_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, lean_box(0));
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__0___boxed(lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v_a_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__0(v___x_442_, v___x_443_, v_a_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v_a_444_);
return v_res_452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__0(void){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_instMonadEIO___redArg();
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__0);
v___x_455_ = l_StateRefT_x27_instMonad___redArg(v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__1___boxed(lean_object* v_acc_460_, lean_object* v_declInfos_461_, lean_object* v_k_462_, lean_object* v_kind_463_, lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v_kind_boxed_472_; lean_object* v_res_473_; 
v_kind_boxed_472_ = lean_unbox(v_kind_463_);
v_res_473_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__1(v_acc_460_, v_declInfos_461_, v_k_462_, v_kind_boxed_472_, v_x_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8(lean_object* v_declInfos_474_, lean_object* v_k_475_, uint8_t v_kind_476_, lean_object* v_acc_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; lean_object* v_toApplicative_486_; lean_object* v_toFunctor_487_; lean_object* v_toSeq_488_; lean_object* v_toSeqLeft_489_; lean_object* v_toSeqRight_490_; lean_object* v___f_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v_toApplicative_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_554_; 
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__1);
v_toApplicative_486_ = lean_ctor_get(v___x_485_, 0);
v_toFunctor_487_ = lean_ctor_get(v_toApplicative_486_, 0);
v_toSeq_488_ = lean_ctor_get(v_toApplicative_486_, 2);
v_toSeqLeft_489_ = lean_ctor_get(v_toApplicative_486_, 3);
v_toSeqRight_490_ = lean_ctor_get(v_toApplicative_486_, 4);
v___f_491_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__2));
v___f_492_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__3));
lean_inc_ref_n(v_toFunctor_487_, 2);
v___f_493_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_493_, 0, v_toFunctor_487_);
v___f_494_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_494_, 0, v_toFunctor_487_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___f_493_);
lean_ctor_set(v___x_495_, 1, v___f_494_);
lean_inc(v_toSeqRight_490_);
v___f_496_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_496_, 0, v_toSeqRight_490_);
lean_inc(v_toSeqLeft_489_);
v___f_497_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_497_, 0, v_toSeqLeft_489_);
lean_inc(v_toSeq_488_);
v___f_498_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_498_, 0, v_toSeq_488_);
v___x_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_499_, 0, v___x_495_);
lean_ctor_set(v___x_499_, 1, v___f_491_);
lean_ctor_set(v___x_499_, 2, v___f_498_);
lean_ctor_set(v___x_499_, 3, v___f_497_);
lean_ctor_set(v___x_499_, 4, v___f_496_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___f_492_);
v___x_501_ = l_StateRefT_x27_instMonad___redArg(v___x_500_);
v_toApplicative_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_501_, 1);
lean_dec(v_unused_555_);
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_554_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_toApplicative_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_554_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_toFunctor_506_; lean_object* v_toSeq_507_; lean_object* v_toSeqLeft_508_; lean_object* v_toSeqRight_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_552_; 
v_toFunctor_506_ = lean_ctor_get(v_toApplicative_502_, 0);
v_toSeq_507_ = lean_ctor_get(v_toApplicative_502_, 2);
v_toSeqLeft_508_ = lean_ctor_get(v_toApplicative_502_, 3);
v_toSeqRight_509_ = lean_ctor_get(v_toApplicative_502_, 4);
v_isSharedCheck_552_ = !lean_is_exclusive(v_toApplicative_502_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_toApplicative_502_, 1);
lean_dec(v_unused_553_);
v___x_511_ = v_toApplicative_502_;
v_isShared_512_ = v_isSharedCheck_552_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_toSeqRight_509_);
lean_inc(v_toSeqLeft_508_);
lean_inc(v_toSeq_507_);
lean_inc(v_toFunctor_506_);
lean_dec(v_toApplicative_502_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_552_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___f_513_; lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___f_518_; lean_object* v___f_519_; lean_object* v___f_520_; lean_object* v___x_522_; 
v___f_513_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__4));
v___f_514_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___closed__5));
lean_inc_ref(v_toFunctor_506_);
v___f_515_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_515_, 0, v_toFunctor_506_);
v___f_516_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_516_, 0, v_toFunctor_506_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___f_515_);
lean_ctor_set(v___x_517_, 1, v___f_516_);
v___f_518_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_518_, 0, v_toSeqRight_509_);
v___f_519_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_519_, 0, v_toSeqLeft_508_);
v___f_520_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_520_, 0, v_toSeq_507_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 4, v___f_518_);
lean_ctor_set(v___x_511_, 3, v___f_519_);
lean_ctor_set(v___x_511_, 2, v___f_520_);
lean_ctor_set(v___x_511_, 1, v___f_513_);
lean_ctor_set(v___x_511_, 0, v___x_517_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___f_513_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v___f_520_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v___f_519_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v___f_518_);
v___x_522_ = v_reuseFailAlloc_551_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___f_514_);
lean_ctor_set(v___x_504_, 0, v___x_522_);
v___x_524_ = v___x_504_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___f_514_);
v___x_524_ = v_reuseFailAlloc_550_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_525_ = l_StateRefT_x27_instMonad___redArg(v___x_524_);
v___x_526_ = l_ReaderT_instMonad___redArg(v___x_525_);
v___x_527_ = lean_array_get_size(v_acc_477_);
v___x_528_ = lean_array_get_size(v_declInfos_474_);
v___x_529_ = lean_nat_dec_lt(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_dec_ref(v___x_526_);
lean_dec_ref(v_declInfos_474_);
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
lean_inc(v___y_481_);
lean_inc_ref(v___y_480_);
lean_inc(v___y_479_);
lean_inc_ref(v___y_478_);
v___x_530_ = lean_apply_8(v_k_475_, v_acc_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, lean_box(0));
return v___x_530_;
}
else
{
lean_object* v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___f_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_snd_540_; lean_object* v_fst_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v___x_531_ = lean_box(0);
v___x_532_ = 0;
v___x_533_ = l_Lean_instInhabitedExpr;
v___f_534_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__0___boxed), 10, 2);
lean_closure_set(v___f_534_, 0, v___x_526_);
lean_closure_set(v___f_534_, 1, v___x_533_);
v___f_535_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_535_, 0, v___f_534_);
v___x_536_ = lean_box(v___x_532_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___f_535_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_531_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_array_get(v___x_538_, v_declInfos_474_, v___x_527_);
lean_dec_ref_known(v___x_538_, 2);
v_snd_540_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_snd_540_);
v_fst_541_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_fst_541_);
lean_dec(v___x_539_);
v_fst_542_ = lean_ctor_get(v_snd_540_, 0);
lean_inc(v_fst_542_);
v_snd_543_ = lean_ctor_get(v_snd_540_, 1);
lean_inc(v_snd_543_);
lean_dec(v_snd_540_);
v___x_544_ = lean_box(v_kind_476_);
lean_inc_ref(v_acc_477_);
v___f_545_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__1___boxed), 12, 4);
lean_closure_set(v___f_545_, 0, v_acc_477_);
lean_closure_set(v___f_545_, 1, v_declInfos_474_);
lean_closure_set(v___f_545_, 2, v_k_475_);
lean_closure_set(v___f_545_, 3, v___x_544_);
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
lean_inc(v___y_481_);
lean_inc_ref(v___y_480_);
lean_inc(v___y_479_);
lean_inc_ref(v___y_478_);
v___x_546_ = lean_apply_8(v_snd_543_, v_acc_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, lean_box(0));
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; uint8_t v___x_548_; lean_object* v___x_549_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_unbox(v_fst_542_);
lean_dec(v_fst_542_);
v___x_549_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg(v_fst_541_, v___x_548_, v_a_547_, v___f_545_, v_kind_476_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
return v___x_549_;
}
else
{
lean_dec_ref(v___f_545_);
lean_dec(v_fst_542_);
lean_dec(v_fst_541_);
return v___x_546_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___lam__1(lean_object* v_acc_556_, lean_object* v_declInfos_557_, lean_object* v_k_558_, uint8_t v_kind_559_, lean_object* v_x_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_array_push(v_acc_556_, v_x_560_);
v___x_569_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8(v_declInfos_557_, v_k_558_, v_kind_559_, v___x_568_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_declInfos_570_, lean_object* v_k_571_, lean_object* v_kind_572_, lean_object* v_acc_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_kind_boxed_581_; lean_object* v_res_582_; 
v_kind_boxed_581_ = lean_unbox(v_kind_572_);
v_res_582_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8(v_declInfos_570_, v_k_571_, v_kind_boxed_581_, v_acc_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6(lean_object* v_declInfos_585_, lean_object* v_k_586_, uint8_t v_kind_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0));
v___x_596_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8(v_declInfos_585_, v_k_586_, v_kind_587_, v___x_595_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___boxed(lean_object* v_declInfos_597_, lean_object* v_k_598_, lean_object* v_kind_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v_kind_boxed_607_; lean_object* v_res_608_; 
v_kind_boxed_607_ = lean_unbox(v_kind_599_);
v_res_608_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6(v_declInfos_597_, v_k_598_, v_kind_boxed_607_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__5(size_t v_sz_609_, size_t v_i_610_, lean_object* v_bs_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = lean_usize_dec_lt(v_i_610_, v_sz_609_);
if (v___x_612_ == 0)
{
return v_bs_611_;
}
else
{
lean_object* v_v_613_; lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_631_; 
v_v_613_ = lean_array_uget(v_bs_611_, v_i_610_);
v_fst_614_ = lean_ctor_get(v_v_613_, 0);
v_snd_615_ = lean_ctor_get(v_v_613_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_v_613_);
if (v_isSharedCheck_631_ == 0)
{
v___x_617_ = v_v_613_;
v_isShared_618_ = v_isSharedCheck_631_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snd_615_);
lean_inc(v_fst_614_);
lean_dec(v_v_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_631_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v_bs_x27_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v_bs_x27_620_ = lean_array_uset(v_bs_611_, v_i_610_, v___x_619_);
v___x_621_ = 0;
v___x_622_ = lean_box(v___x_621_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_622_);
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_snd_615_);
v___x_624_ = v_reuseFailAlloc_630_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; 
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_fst_614_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_610_, v___x_626_);
v___x_628_ = lean_array_uset(v_bs_x27_620_, v_i_610_, v___x_625_);
v_i_610_ = v___x_627_;
v_bs_611_ = v___x_628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_bs_634_){
_start:
{
size_t v_sz_boxed_635_; size_t v_i_boxed_636_; lean_object* v_res_637_; 
v_sz_boxed_635_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_636_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__5(v_sz_boxed_635_, v_i_boxed_636_, v_bs_634_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4(lean_object* v_declInfos_638_, lean_object* v_k_639_, uint8_t v_kind_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
size_t v_sz_648_; size_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_sz_648_ = lean_array_size(v_declInfos_638_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__5(v_sz_648_, v___x_649_, v_declInfos_638_);
v___x_651_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6(v___x_650_, v_k_639_, v_kind_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4___boxed(lean_object* v_declInfos_652_, lean_object* v_k_653_, lean_object* v_kind_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
uint8_t v_kind_boxed_662_; lean_object* v_res_663_; 
v_kind_boxed_662_ = lean_unbox(v_kind_654_);
v_res_663_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4(v_declInfos_652_, v_k_653_, v_kind_boxed_662_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3(lean_object* v_declInfos_664_, lean_object* v_k_665_, uint8_t v_kind_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
size_t v_sz_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_sz_674_ = lean_array_size(v_declInfos_664_);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__3(v_sz_674_, v___x_675_, v_declInfos_664_);
v___x_677_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4(v___x_676_, v_k_665_, v_kind_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3___boxed(lean_object* v_declInfos_678_, lean_object* v_k_679_, lean_object* v_kind_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v_kind_boxed_688_; lean_object* v_res_689_; 
v_kind_boxed_688_ = lean_unbox(v_kind_680_);
v_res_689_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3(v_declInfos_678_, v_k_679_, v_kind_boxed_688_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__2(lean_object* v_as_690_, size_t v_sz_691_, size_t v_i_692_, lean_object* v_b_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_a_702_; uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_692_, v_sz_691_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_b_693_);
return v___x_707_;
}
else
{
lean_object* v_snd_708_; lean_object* v_fst_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_755_; 
v_snd_708_ = lean_ctor_get(v_b_693_, 1);
v_fst_709_ = lean_ctor_get(v_b_693_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_b_693_);
if (v_isSharedCheck_755_ == 0)
{
v___x_711_ = v_b_693_;
v_isShared_712_ = v_isSharedCheck_755_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_snd_708_);
lean_inc(v_fst_709_);
lean_dec(v_b_693_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_755_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_array_713_; lean_object* v_start_714_; lean_object* v_stop_715_; uint8_t v___x_716_; 
v_array_713_ = lean_ctor_get(v_snd_708_, 0);
v_start_714_ = lean_ctor_get(v_snd_708_, 1);
v_stop_715_ = lean_ctor_get(v_snd_708_, 2);
v___x_716_ = lean_nat_dec_lt(v_start_714_, v_stop_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_718_; 
if (v_isShared_712_ == 0)
{
v___x_718_ = v___x_711_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_snd_708_);
v___x_718_ = v_reuseFailAlloc_720_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; 
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
else
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_751_; 
lean_inc(v_stop_715_);
lean_inc(v_start_714_);
lean_inc_ref(v_array_713_);
v_isSharedCheck_751_ = !lean_is_exclusive(v_snd_708_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_752_ = lean_ctor_get(v_snd_708_, 2);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_snd_708_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_snd_708_, 0);
lean_dec(v_unused_754_);
v___x_722_ = v_snd_708_;
v_isShared_723_ = v_isSharedCheck_751_;
goto v_resetjp_721_;
}
else
{
lean_dec(v_snd_708_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_751_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_724_ = lean_array_fget(v_array_713_, v_start_714_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_start_714_, v___x_725_);
lean_dec(v_start_714_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_array_713_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_stop_715_);
v___x_728_ = v_reuseFailAlloc_750_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
uint8_t v___x_729_; 
v___x_729_ = lean_unbox(v___x_724_);
lean_dec(v___x_724_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v___x_728_);
v___x_731_ = v___x_711_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_728_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v_a_702_ = v___x_731_;
goto v___jp_701_;
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_array_uget_borrowed(v_as_690_, v_i_692_);
lean_inc(v_a_733_);
v___x_734_ = l_Lean_Meta_Sym_inferType(v_a_733_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = lean_box(0);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v_a_735_);
lean_ctor_set(v___x_711_, 0, v___x_736_);
v___x_738_ = v___x_711_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_a_735_);
v___x_738_ = v_reuseFailAlloc_741_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_array_push(v_fst_709_, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_728_);
v_a_702_ = v___x_740_;
goto v___jp_701_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec_ref(v___x_728_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
v_a_742_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_734_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_734_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
}
}
}
v___jp_701_:
{
size_t v___x_703_; size_t v___x_704_; 
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_add(v_i_692_, v___x_703_);
v_i_692_ = v___x_704_;
v_b_693_ = v_a_702_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__2___boxed(lean_object* v_as_756_, lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v_sz_boxed_767_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_768_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__2(v_as_756_, v_sz_boxed_767_, v_i_boxed_768_, v_b_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v_as_756_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___redArg(lean_object* v_patternVars_770_, lean_object* v_as_771_, size_t v_sz_772_, size_t v_i_773_, lean_object* v_b_774_){
_start:
{
lean_object* v_a_777_; uint8_t v___x_781_; 
v___x_781_ = lean_usize_dec_lt(v_i_773_, v_sz_772_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v_b_774_);
return v___x_782_;
}
else
{
lean_object* v_snd_783_; lean_object* v_snd_784_; lean_object* v_fst_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_838_; 
v_snd_783_ = lean_ctor_get(v_b_774_, 1);
lean_inc(v_snd_783_);
v_snd_784_ = lean_ctor_get(v_snd_783_, 1);
lean_inc(v_snd_784_);
v_fst_785_ = lean_ctor_get(v_b_774_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_774_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_b_774_, 1);
lean_dec(v_unused_839_);
v___x_787_ = v_b_774_;
v_isShared_788_ = v_isSharedCheck_838_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_fst_785_);
lean_dec(v_b_774_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_838_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_fst_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_836_; 
v_fst_789_ = lean_ctor_get(v_snd_783_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_snd_783_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_snd_783_, 1);
lean_dec(v_unused_837_);
v___x_791_ = v_snd_783_;
v_isShared_792_ = v_isSharedCheck_836_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_fst_789_);
lean_dec(v_snd_783_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_836_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_array_793_; lean_object* v_start_794_; lean_object* v_stop_795_; uint8_t v___x_796_; 
v_array_793_ = lean_ctor_get(v_snd_784_, 0);
v_start_794_ = lean_ctor_get(v_snd_784_, 1);
v_stop_795_ = lean_ctor_get(v_snd_784_, 2);
v___x_796_ = lean_nat_dec_lt(v_start_794_, v_stop_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_798_; 
if (v_isShared_792_ == 0)
{
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_snd_784_);
v___x_798_ = v_reuseFailAlloc_803_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_798_);
v___x_800_ = v___x_787_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_785_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
else
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_832_; 
lean_inc(v_stop_795_);
lean_inc(v_start_794_);
lean_inc_ref(v_array_793_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_snd_784_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; 
v_unused_833_ = lean_ctor_get(v_snd_784_, 2);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_snd_784_, 1);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_snd_784_, 0);
lean_dec(v_unused_835_);
v___x_805_ = v_snd_784_;
v_isShared_806_ = v_isSharedCheck_832_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_snd_784_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_832_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_807_ = lean_array_fget(v_array_793_, v_start_794_);
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = lean_nat_add(v_start_794_, v___x_808_);
lean_dec(v_start_794_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_809_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_array_793_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_stop_795_);
v___x_811_ = v_reuseFailAlloc_831_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
uint8_t v___x_812_; 
v___x_812_ = lean_unbox(v___x_807_);
lean_dec(v___x_807_);
if (v___x_812_ == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v_a_813_ = lean_array_uget_borrowed(v_as_771_, v_i_773_);
lean_inc(v_a_813_);
v___x_814_ = lean_array_push(v_fst_785_, v_a_813_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_811_);
v___x_816_ = v___x_791_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_789_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_811_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_816_);
lean_ctor_set(v___x_787_, 0, v___x_814_);
v___x_818_ = v___x_787_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_a_777_ = v___x_818_;
goto v___jp_776_;
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_821_ = l_Lean_instInhabitedExpr;
v___x_822_ = lean_array_get_borrowed(v___x_821_, v_patternVars_770_, v_fst_789_);
v___x_823_ = lean_nat_add(v_fst_789_, v___x_808_);
lean_dec(v_fst_789_);
lean_inc(v___x_822_);
v___x_824_ = lean_array_push(v_fst_785_, v___x_822_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v___x_811_);
lean_ctor_set(v___x_791_, 0, v___x_823_);
v___x_826_ = v___x_791_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_811_);
v___x_826_ = v_reuseFailAlloc_830_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_826_);
lean_ctor_set(v___x_787_, 0, v___x_824_);
v___x_828_ = v___x_787_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_a_777_ = v___x_828_;
goto v___jp_776_;
}
}
}
}
}
}
}
}
}
v___jp_776_:
{
size_t v___x_778_; size_t v___x_779_; 
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_773_, v___x_778_);
v_i_773_ = v___x_779_;
v_b_774_ = v_a_777_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___redArg___boxed(lean_object* v_patternVars_840_, lean_object* v_as_841_, lean_object* v_sz_842_, lean_object* v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_){
_start:
{
size_t v_sz_boxed_846_; size_t v_i_boxed_847_; lean_object* v_res_848_; 
v_sz_boxed_846_ = lean_unbox_usize(v_sz_842_);
lean_dec(v_sz_842_);
v_i_boxed_847_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_res_848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___redArg(v_patternVars_840_, v_as_841_, v_sz_boxed_846_, v_i_boxed_847_, v_b_844_);
lean_dec_ref(v_as_841_);
lean_dec_ref(v_patternVars_840_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___lam__0(lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v_x_851_, lean_object* v_x_852_, uint8_t v___x_853_, lean_object* v_patternVars_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; size_t v_sz_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_862_ = lean_mk_empty_array_with_capacity(v___x_849_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_849_);
lean_ctor_set(v___x_863_, 1, v___x_850_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v_sz_865_ = lean_array_size(v_x_851_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___redArg(v_patternVars_854_, v_x_851_, v_sz_865_, v___x_866_, v___x_864_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_fst_869_; lean_object* v___x_870_; uint8_t v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_fst_869_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_fst_869_);
lean_dec(v_a_868_);
v___x_870_ = l_Lean_mkAppN(v_x_852_, v_fst_869_);
lean_dec(v_fst_869_);
v___x_871_ = 0;
v___x_872_ = 1;
v___x_873_ = l_Lean_Meta_mkLambdaFVars(v_patternVars_854_, v___x_870_, v___x_871_, v___x_853_, v___x_871_, v___x_853_, v___x_872_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = l_Lean_Meta_Sym_shareCommonInc(v_a_874_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_875_;
}
else
{
return v___x_873_;
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v_x_852_);
v_a_876_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_867_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___lam__0___boxed(lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v___x_888_, lean_object* v_patternVars_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v___x_6943__boxed_897_; lean_object* v_res_898_; 
v___x_6943__boxed_897_ = lean_unbox(v___x_888_);
v_res_898_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___lam__0(v___x_884_, v___x_885_, v_x_886_, v_x_887_, v___x_6943__boxed_897_, v_patternVars_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v_patternVars_889_);
lean_dec_ref(v_x_886_);
return v_res_898_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__3(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_902_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__2));
v___x_903_ = lean_unsigned_to_nat(6u);
v___x_904_ = lean_unsigned_to_nat(89u);
v___x_905_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__1));
v___x_906_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__0));
v___x_907_ = l_mkPanicMessageWithDecl(v___x_906_, v___x_905_, v___x_904_, v___x_903_, v___x_902_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4(lean_object* v_mask_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
if (lean_obj_tag(v_x_911_) == 5)
{
lean_object* v_fn_921_; lean_object* v_arg_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_fn_921_ = lean_ctor_get(v_x_911_, 0);
lean_inc_ref(v_fn_921_);
v_arg_922_ = lean_ctor_get(v_x_911_, 1);
lean_inc_ref(v_arg_922_);
lean_dec_ref_known(v_x_911_, 2);
v___x_923_ = lean_array_set(v_x_912_, v_x_913_, v_arg_922_);
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_sub(v_x_913_, v___x_924_);
lean_dec(v_x_913_);
v_x_911_ = v_fn_921_;
v_x_912_ = v___x_923_;
v_x_913_ = v___x_925_;
goto _start;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
lean_dec(v_x_913_);
v___x_927_ = lean_array_get_size(v_x_912_);
v___x_928_ = lean_array_get_size(v_mask_910_);
v___x_929_ = lean_nat_dec_eq(v___x_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_x_912_);
lean_dec_ref(v_x_911_);
lean_dec_ref(v_mask_910_);
v___x_930_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__3);
v___x_931_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__0(v___x_930_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v_decls_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___f_936_; lean_object* v___x_937_; size_t v_sz_938_; size_t v___x_939_; lean_object* v___x_940_; 
v___x_932_ = lean_unsigned_to_nat(0u);
v_decls_933_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___closed__4));
v___x_934_ = l_Array_toSubarray___redArg(v_mask_910_, v___x_932_, v___x_928_);
v___x_935_ = lean_box(v___x_929_);
lean_inc_ref(v_x_912_);
lean_inc_ref(v___x_934_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_936_, 0, v___x_932_);
lean_closure_set(v___f_936_, 1, v___x_934_);
lean_closure_set(v___f_936_, 2, v_x_912_);
lean_closure_set(v___f_936_, 3, v_x_911_);
lean_closure_set(v___f_936_, 4, v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_decls_933_);
lean_ctor_set(v___x_937_, 1, v___x_934_);
v_sz_938_ = lean_array_size(v_x_912_);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__2(v_x_912_, v_sz_938_, v___x_939_, v___x_937_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec_ref(v_x_912_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_fst_942_; uint8_t v___x_943_; lean_object* v___x_944_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v_fst_942_ = lean_ctor_get(v_a_941_, 0);
lean_inc(v_fst_942_);
lean_dec(v_a_941_);
v___x_943_ = 0;
v___x_944_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3(v_fst_942_, v___f_936_, v___x_943_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_944_;
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v___f_936_);
v_a_945_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_940_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_940_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4___boxed(lean_object* v_mask_953_, lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4(v_mask_953_, v_x_954_, v_x_955_, v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0(void){
_start:
{
lean_object* v___x_965_; lean_object* v_dummy_966_; 
v___x_965_ = lean_box(0);
v_dummy_966_ = l_Lean_Expr_sort___override(v___x_965_);
return v_dummy_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern(lean_object* v_funAtom_967_, lean_object* v_mask_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_dummy_976_; lean_object* v_nargs_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_dummy_976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0);
v_nargs_977_ = l_Lean_Expr_getAppNumArgs(v_funAtom_967_);
lean_inc(v_nargs_977_);
v___x_978_ = lean_mk_array(v_nargs_977_, v_dummy_976_);
v___x_979_ = lean_unsigned_to_nat(1u);
v___x_980_ = lean_nat_sub(v_nargs_977_, v___x_979_);
lean_dec(v_nargs_977_);
v___x_981_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__4(v_mask_968_, v_funAtom_967_, v___x_978_, v___x_980_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___boxed(lean_object* v_funAtom_982_, lean_object* v_mask_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern(v_funAtom_982_, v_mask_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1(lean_object* v_patternVars_992_, lean_object* v_as_993_, size_t v_sz_994_, size_t v_i_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___redArg(v_patternVars_992_, v_as_993_, v_sz_994_, v_i_995_, v_b_996_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1___boxed(lean_object* v_patternVars_1005_, lean_object* v_as_1006_, lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
size_t v_sz_boxed_1017_; size_t v_i_boxed_1018_; lean_object* v_res_1019_; 
v_sz_boxed_1017_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1018_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__1(v_patternVars_1005_, v_as_1006_, v_sz_boxed_1017_, v_i_boxed_1018_, v_b_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_as_1006_);
lean_dec_ref(v_patternVars_1005_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9(lean_object* v_00_u03b1_1020_, lean_object* v_name_1021_, uint8_t v_bi_1022_, lean_object* v_type_1023_, lean_object* v_k_1024_, uint8_t v_kind_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___redArg(v_name_1021_, v_bi_1022_, v_type_1023_, v_k_1024_, v_kind_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_name_1035_, lean_object* v_bi_1036_, lean_object* v_type_1037_, lean_object* v_k_1038_, lean_object* v_kind_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_bi_boxed_1047_; uint8_t v_kind_boxed_1048_; lean_object* v_res_1049_; 
v_bi_boxed_1047_ = lean_unbox(v_bi_1036_);
v_kind_boxed_1048_ = lean_unbox(v_kind_1039_);
v_res_1049_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6_spec__8_spec__9(v_00_u03b1_1034_, v_name_1035_, v_bi_boxed_1047_, v_type_1037_, v_k_1038_, v_kind_boxed_1048_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___redArg(lean_object* v_as_1050_, size_t v_sz_1051_, size_t v_i_1052_, lean_object* v_b_1053_){
_start:
{
lean_object* v_a_1056_; uint8_t v___x_1060_; 
v___x_1060_ = lean_usize_dec_lt(v_i_1052_, v_sz_1051_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_b_1053_);
return v___x_1061_;
}
else
{
lean_object* v_snd_1062_; lean_object* v_fst_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1097_; 
v_snd_1062_ = lean_ctor_get(v_b_1053_, 1);
v_fst_1063_ = lean_ctor_get(v_b_1053_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_b_1053_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1065_ = v_b_1053_;
v_isShared_1066_ = v_isSharedCheck_1097_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_snd_1062_);
lean_inc(v_fst_1063_);
lean_dec(v_b_1053_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1097_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_array_1067_; lean_object* v_start_1068_; lean_object* v_stop_1069_; uint8_t v___x_1070_; 
v_array_1067_ = lean_ctor_get(v_snd_1062_, 0);
v_start_1068_ = lean_ctor_get(v_snd_1062_, 1);
v_stop_1069_ = lean_ctor_get(v_snd_1062_, 2);
v___x_1070_ = lean_nat_dec_lt(v_start_1068_, v_stop_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1072_; 
if (v_isShared_1066_ == 0)
{
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_fst_1063_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_snd_1062_);
v___x_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
else
{
lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1093_; 
lean_inc(v_stop_1069_);
lean_inc(v_start_1068_);
lean_inc_ref(v_array_1067_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_snd_1062_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1094_ = lean_ctor_get(v_snd_1062_, 2);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_snd_1062_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_snd_1062_, 0);
lean_dec(v_unused_1096_);
v___x_1076_ = v_snd_1062_;
v_isShared_1077_ = v_isSharedCheck_1093_;
goto v_resetjp_1075_;
}
else
{
lean_dec(v_snd_1062_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1093_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1078_ = lean_array_fget(v_array_1067_, v_start_1068_);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_start_1068_, v___x_1079_);
lean_dec(v_start_1068_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1080_);
v___x_1082_ = v___x_1076_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_array_1067_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_stop_1069_);
v___x_1082_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_unbox(v___x_1078_);
lean_dec(v___x_1078_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1085_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1082_);
v___x_1085_ = v___x_1065_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_fst_1063_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1082_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
v_a_1056_ = v___x_1085_;
goto v___jp_1055_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v_a_1087_ = lean_array_uget_borrowed(v_as_1050_, v_i_1052_);
lean_inc(v_a_1087_);
v___x_1088_ = lean_array_push(v_fst_1063_, v_a_1087_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1082_);
lean_ctor_set(v___x_1065_, 0, v___x_1088_);
v___x_1090_ = v___x_1065_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1082_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
v_a_1056_ = v___x_1090_;
goto v___jp_1055_;
}
}
}
}
}
}
}
v___jp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1052_, v___x_1057_);
v_i_1052_ = v___x_1058_;
v_b_1053_ = v_a_1056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___redArg___boxed(lean_object* v_as_1098_, lean_object* v_sz_1099_, lean_object* v_i_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_){
_start:
{
size_t v_sz_boxed_1103_; size_t v_i_boxed_1104_; lean_object* v_res_1105_; 
v_sz_boxed_1103_ = lean_unbox_usize(v_sz_1099_);
lean_dec(v_sz_1099_);
v_i_boxed_1104_ = lean_unbox_usize(v_i_1100_);
lean_dec(v_i_1100_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___redArg(v_as_1098_, v_sz_boxed_1103_, v_i_boxed_1104_, v_b_1101_);
lean_dec_ref(v_as_1098_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__2(lean_object* v___x_1106_, size_t v_sz_1107_, size_t v_i_1108_, lean_object* v_bs_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_lt(v_i_1108_, v_sz_1107_);
if (v___x_1110_ == 0)
{
return v_bs_1109_;
}
else
{
lean_object* v_v_1111_; lean_object* v_fst_1112_; lean_object* v_snd_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; uint8_t v___y_1117_; uint8_t v___x_1123_; 
v_v_1111_ = lean_array_uget_borrowed(v_bs_1109_, v_i_1108_);
v_fst_1112_ = lean_ctor_get(v_v_1111_, 0);
lean_inc(v_fst_1112_);
v_snd_1113_ = lean_ctor_get(v_v_1111_, 1);
lean_inc(v_snd_1113_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1109_, v_i_1108_, v___x_1114_);
v___x_1123_ = lean_unbox(v_fst_1112_);
lean_dec(v_fst_1112_);
if (v___x_1123_ == 0)
{
uint8_t v___x_1124_; 
lean_dec(v_snd_1113_);
v___x_1124_ = lean_nat_dec_eq(v___x_1106_, v___x_1114_);
v___y_1117_ = v___x_1124_;
goto v___jp_1116_;
}
else
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_unbox(v_snd_1113_);
lean_dec(v_snd_1113_);
v___y_1117_ = v___x_1125_;
goto v___jp_1116_;
}
v___jp_1116_:
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1108_, v___x_1118_);
v___x_1120_ = lean_box(v___y_1117_);
v___x_1121_ = lean_array_uset(v_bs_x27_1115_, v_i_1108_, v___x_1120_);
v_i_1108_ = v___x_1119_;
v_bs_1109_ = v___x_1121_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__2___boxed(lean_object* v___x_1126_, lean_object* v_sz_1127_, lean_object* v_i_1128_, lean_object* v_bs_1129_){
_start:
{
size_t v_sz_boxed_1130_; size_t v_i_boxed_1131_; lean_object* v_res_1132_; 
v_sz_boxed_1130_ = lean_unbox_usize(v_sz_1127_);
lean_dec(v_sz_1127_);
v_i_boxed_1131_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__2(v___x_1126_, v_sz_boxed_1130_, v_i_boxed_1131_, v_bs_1129_);
lean_dec(v___x_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___redArg(uint8_t v___x_1133_, size_t v_sz_1134_, size_t v_i_1135_, lean_object* v_bs_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_usize_dec_lt(v_i_1135_, v_sz_1134_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_bs_1136_);
return v___x_1145_;
}
else
{
lean_object* v_v_1146_; lean_object* v___x_1147_; lean_object* v_bs_x27_1148_; uint8_t v_a_1150_; lean_object* v___x_1156_; 
v_v_1146_ = lean_array_uget(v_bs_1136_, v_i_1135_);
v___x_1147_ = lean_unsigned_to_nat(0u);
v_bs_x27_1148_ = lean_array_uset(v_bs_1136_, v_i_1135_, v___x_1147_);
lean_inc(v_v_1146_);
v___x_1156_ = l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg(v_v_1146_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
if (lean_obj_tag(v_a_1157_) == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg(v_v_1146_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; uint8_t v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_unbox(v_a_1159_);
lean_dec(v_a_1159_);
v_a_1150_ = v___x_1160_;
goto v___jp_1149_;
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_bs_x27_1148_);
v_a_1161_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1158_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1158_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_1157_, 1);
lean_dec(v_v_1146_);
v_a_1150_ = v___x_1133_;
goto v___jp_1149_;
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_bs_x27_1148_);
lean_dec(v_v_1146_);
v_a_1169_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1156_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1156_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
v___jp_1149_:
{
size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1135_, v___x_1151_);
v___x_1153_ = lean_box(v_a_1150_);
v___x_1154_ = lean_array_uset(v_bs_x27_1148_, v_i_1135_, v___x_1153_);
v_i_1135_ = v___x_1152_;
v_bs_1136_ = v___x_1154_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___redArg___boxed(lean_object* v___x_1177_, lean_object* v_sz_1178_, lean_object* v_i_1179_, lean_object* v_bs_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v___x_93979__boxed_1188_; size_t v_sz_boxed_1189_; size_t v_i_boxed_1190_; lean_object* v_res_1191_; 
v___x_93979__boxed_1188_ = lean_unbox(v___x_1177_);
v_sz_boxed_1189_ = lean_unbox_usize(v_sz_1178_);
lean_dec(v_sz_1178_);
v_i_boxed_1190_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___redArg(v___x_93979__boxed_1188_, v_sz_boxed_1189_, v_i_boxed_1190_, v_bs_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5_spec__5(lean_object* v_msgData_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v_env_1199_; lean_object* v___x_1200_; lean_object* v_toCold_1201_; lean_object* v_mctx_1202_; lean_object* v_lctx_1203_; lean_object* v_options_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1198_ = lean_st_ref_get(v___y_1196_);
v_env_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc_ref(v_env_1199_);
lean_dec(v___x_1198_);
v___x_1200_ = lean_st_ref_get(v___y_1194_);
v_toCold_1201_ = lean_ctor_get(v___y_1195_, 0);
v_mctx_1202_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_mctx_1202_);
lean_dec(v___x_1200_);
v_lctx_1203_ = lean_ctor_get(v___y_1193_, 2);
v_options_1204_ = lean_ctor_get(v_toCold_1201_, 2);
lean_inc_ref(v_options_1204_);
lean_inc_ref(v_lctx_1203_);
v___x_1205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1205_, 0, v_env_1199_);
lean_ctor_set(v___x_1205_, 1, v_mctx_1202_);
lean_ctor_set(v___x_1205_, 2, v_lctx_1203_);
lean_ctor_set(v___x_1205_, 3, v_options_1204_);
v___x_1206_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v_msgData_1192_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5_spec__5___boxed(lean_object* v_msgData_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5_spec__5(v_msgData_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1214_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1215_; double v___x_1216_; 
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_float_of_nat(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg(lean_object* v_cls_1220_, lean_object* v_msg_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_ref_1227_; lean_object* v___x_1228_; lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1274_; 
v_ref_1227_ = lean_ctor_get(v___y_1224_, 2);
v___x_1228_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5_spec__5(v_msg_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1274_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1274_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v_traceState_1234_; lean_object* v_env_1235_; lean_object* v_nextMacroScope_1236_; lean_object* v_ngen_1237_; lean_object* v_auxDeclNGen_1238_; lean_object* v_cache_1239_; lean_object* v_recordedDeps_1240_; lean_object* v_messages_1241_; lean_object* v_infoState_1242_; lean_object* v_snapshotTasks_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1273_; 
v___x_1233_ = lean_st_ref_take(v___y_1225_);
v_traceState_1234_ = lean_ctor_get(v___x_1233_, 4);
v_env_1235_ = lean_ctor_get(v___x_1233_, 0);
v_nextMacroScope_1236_ = lean_ctor_get(v___x_1233_, 1);
v_ngen_1237_ = lean_ctor_get(v___x_1233_, 2);
v_auxDeclNGen_1238_ = lean_ctor_get(v___x_1233_, 3);
v_cache_1239_ = lean_ctor_get(v___x_1233_, 5);
v_recordedDeps_1240_ = lean_ctor_get(v___x_1233_, 6);
v_messages_1241_ = lean_ctor_get(v___x_1233_, 7);
v_infoState_1242_ = lean_ctor_get(v___x_1233_, 8);
v_snapshotTasks_1243_ = lean_ctor_get(v___x_1233_, 9);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1245_ = v___x_1233_;
v_isShared_1246_ = v_isSharedCheck_1273_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snapshotTasks_1243_);
lean_inc(v_infoState_1242_);
lean_inc(v_messages_1241_);
lean_inc(v_recordedDeps_1240_);
lean_inc(v_cache_1239_);
lean_inc(v_traceState_1234_);
lean_inc(v_auxDeclNGen_1238_);
lean_inc(v_ngen_1237_);
lean_inc(v_nextMacroScope_1236_);
lean_inc(v_env_1235_);
lean_dec(v___x_1233_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1273_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint64_t v_tid_1247_; lean_object* v_traces_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1272_; 
v_tid_1247_ = lean_ctor_get_uint64(v_traceState_1234_, sizeof(void*)*1);
v_traces_1248_ = lean_ctor_get(v_traceState_1234_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_traceState_1234_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1250_ = v_traceState_1234_;
v_isShared_1251_ = v_isSharedCheck_1272_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_traces_1248_);
lean_dec(v_traceState_1234_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1272_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; double v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__0);
v___x_1255_ = 0;
v___x_1256_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__1));
v___x_1257_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1257_, 0, v_cls_1220_);
lean_ctor_set(v___x_1257_, 1, v___x_1253_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
lean_ctor_set_float(v___x_1257_, sizeof(void*)*3, v___x_1254_);
lean_ctor_set_float(v___x_1257_, sizeof(void*)*3 + 8, v___x_1254_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*3 + 16, v___x_1255_);
v___x_1258_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___closed__2));
v___x_1259_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v_a_1229_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
lean_inc(v_ref_1227_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_ref_1227_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_PersistentArray_push___redArg(v_traces_1248_, v___x_1260_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1261_);
v___x_1263_ = v___x_1250_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1261_);
lean_ctor_set_uint64(v_reuseFailAlloc_1271_, sizeof(void*)*1, v_tid_1247_);
v___x_1263_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 4, v___x_1263_);
v___x_1265_ = v___x_1245_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_env_1235_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_nextMacroScope_1236_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_ngen_1237_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_auxDeclNGen_1238_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v_cache_1239_);
lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_recordedDeps_1240_);
lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_messages_1241_);
lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_infoState_1242_);
lean_ctor_set(v_reuseFailAlloc_1270_, 9, v_snapshotTasks_1243_);
v___x_1265_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_st_ref_put(v___y_1225_, v___x_1265_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1252_);
v___x_1268_ = v___x_1231_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1252_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg___boxed(lean_object* v_cls_1275_, lean_object* v_msg_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg(v_cls_1275_, v_msg_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4(lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
if (lean_obj_tag(v_a_1285_) == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = l_List_reverse___redArg(v_a_1286_);
return v___x_1287_;
}
else
{
lean_object* v_head_1288_; lean_object* v_tail_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1304_; 
v_head_1288_ = lean_ctor_get(v_a_1285_, 0);
v_tail_1289_ = lean_ctor_get(v_a_1285_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_a_1285_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1291_ = v_a_1285_;
v_isShared_1292_ = v_isSharedCheck_1304_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_tail_1289_);
lean_inc(v_head_1288_);
lean_dec(v_a_1285_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1304_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___y_1294_; uint8_t v___x_1301_; 
v___x_1301_ = lean_unbox(v_head_1288_);
lean_dec(v_head_1288_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__0));
v___y_1294_ = v___x_1302_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1303_; 
v___x_1303_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4___closed__1));
v___y_1294_ = v___x_1303_;
goto v___jp_1293_;
}
v___jp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_inc_ref(v___y_1294_);
v___x_1295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___y_1294_);
v___x_1296_ = l_Lean_MessageData_ofFormat(v___x_1295_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 1, v_a_1286_);
lean_ctor_set(v___x_1291_, 0, v___x_1296_);
v___x_1298_ = v___x_1291_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_a_1286_);
v___x_1298_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
v_a_1285_ = v_tail_1289_;
v_a_1286_ = v___x_1298_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__1(lean_object* v___x_1305_, uint8_t v___x_1306_, lean_object* v_as_1307_, size_t v_i_1308_, size_t v_stop_1309_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_usize_dec_eq(v_i_1308_, v_stop_1309_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; uint8_t v___y_1313_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1311_ = 1;
v___x_1317_ = lean_array_uget_borrowed(v_as_1307_, v_i_1308_);
v___x_1318_ = lean_unbox(v___x_1317_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_nat_dec_eq(v___x_1305_, v___x_1319_);
v___y_1313_ = v___x_1320_;
goto v___jp_1312_;
}
else
{
v___y_1313_ = v___x_1306_;
goto v___jp_1312_;
}
v___jp_1312_:
{
if (v___y_1313_ == 0)
{
size_t v___x_1314_; size_t v___x_1315_; 
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_add(v_i_1308_, v___x_1314_);
v_i_1308_ = v___x_1315_;
goto _start;
}
else
{
return v___x_1311_;
}
}
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = 0;
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__1___boxed(lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v_as_1324_, lean_object* v_i_1325_, lean_object* v_stop_1326_){
_start:
{
uint8_t v___x_94239__boxed_1327_; size_t v_i_boxed_1328_; size_t v_stop_boxed_1329_; uint8_t v_res_1330_; lean_object* v_r_1331_; 
v___x_94239__boxed_1327_ = lean_unbox(v___x_1323_);
v_i_boxed_1328_ = lean_unbox_usize(v_i_1325_);
lean_dec(v_i_1325_);
v_stop_boxed_1329_ = lean_unbox_usize(v_stop_1326_);
lean_dec(v_stop_1326_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__1(v___x_1322_, v___x_94239__boxed_1327_, v_as_1324_, v_i_boxed_1328_, v_stop_boxed_1329_);
lean_dec_ref(v_as_1324_);
lean_dec(v___x_1322_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3));
v___x_1343_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__5));
v___x_1344_ = l_Lean_Name_append(v___x_1343_, v___x_1342_);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__7));
v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__10(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__9));
v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6(uint8_t v___x_1351_, lean_object* v_fst_1352_, uint8_t v_snd_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
if (lean_obj_tag(v_x_1354_) == 5)
{
lean_object* v_fn_1370_; lean_object* v_arg_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_fn_1370_ = lean_ctor_get(v_x_1354_, 0);
lean_inc_ref(v_fn_1370_);
v_arg_1371_ = lean_ctor_get(v_x_1354_, 1);
lean_inc_ref(v_arg_1371_);
lean_dec_ref_known(v_x_1354_, 2);
v___x_1372_ = lean_array_set(v_x_1355_, v_x_1356_, v_arg_1371_);
v___x_1373_ = lean_unsigned_to_nat(1u);
v___x_1374_ = lean_nat_sub(v_x_1356_, v___x_1373_);
lean_dec(v_x_1356_);
v_x_1354_ = v_fn_1370_;
v_x_1355_ = v___x_1372_;
v_x_1356_ = v___x_1374_;
goto _start;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
lean_dec(v_x_1356_);
v___x_1376_ = lean_array_get_size(v_x_1355_);
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = lean_nat_dec_eq(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; size_t v_sz_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1379_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3));
v_sz_1380_ = lean_array_size(v_x_1355_);
v___x_1381_ = ((size_t)0ULL);
lean_inc_ref(v_x_1355_);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___redArg(v___x_1351_, v_sz_1380_, v___x_1381_, v_x_1355_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1530_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1530_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1530_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_array_get_size(v_a_1383_);
v___x_1393_ = lean_nat_dec_lt(v___x_1377_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_dec(v_a_1383_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_x_1354_);
lean_dec_ref(v_fst_1352_);
goto v___jp_1387_;
}
else
{
if (v___x_1393_ == 0)
{
lean_dec(v_a_1383_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_x_1354_);
lean_dec_ref(v_fst_1352_);
goto v___jp_1387_;
}
else
{
size_t v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_usize_of_nat(v___x_1392_);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__1(v___x_1376_, v___x_1351_, v_a_1383_, v___x_1381_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec(v_a_1383_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_x_1354_);
lean_dec_ref(v_fst_1352_);
goto v___jp_1387_;
}
else
{
lean_object* v___x_1396_; 
lean_del_object(v___x_1385_);
v___x_1396_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getCongrMask___redArg(v_x_1354_, v_x_1355_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1521_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1521_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1521_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
if (lean_obj_tag(v_a_1397_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1518_; 
v_val_1406_ = lean_ctor_get(v_a_1397_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_a_1397_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1408_ = v_a_1397_;
v_isShared_1409_ = v_isSharedCheck_1518_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_val_1406_);
lean_dec(v_a_1397_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1518_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; size_t v_sz_1411_; lean_object* v___x_1412_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1410_ = l_Array_zip___redArg(v_a_1383_, v_val_1406_);
lean_dec(v_val_1406_);
lean_dec(v_a_1383_);
v_sz_1411_ = lean_array_size(v___x_1410_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__2(v___x_1376_, v_sz_1411_, v___x_1381_, v___x_1410_);
v___x_1451_ = lean_array_get_size(v___x_1412_);
v___x_1452_ = lean_nat_dec_lt(v___x_1377_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_fst_1352_);
goto v___jp_1401_;
}
else
{
if (v___x_1452_ == 0)
{
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_fst_1352_);
goto v___jp_1401_;
}
else
{
size_t v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_usize_of_nat(v___x_1451_);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__1(v___x_1376_, v___x_1351_, v___x_1412_, v___x_1381_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_fst_1352_);
goto v___jp_1401_;
}
else
{
lean_object* v___x_1455_; 
lean_del_object(v___x_1399_);
lean_inc_ref(v___x_1412_);
lean_inc_ref(v_fst_1352_);
v___x_1455_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern(v_fst_1352_, v___x_1412_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; lean_object* v_theoryState_1458_; lean_object* v_atoms_1459_; lean_object* v_atomsAssignmentExprCache_1460_; lean_object* v_atomsAssignmentMapCache_1461_; lean_object* v_evalsAtCache_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1509_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = lean_st_ref_take(v___y_1359_);
v_theoryState_1458_ = lean_ctor_get(v___x_1457_, 4);
v_atoms_1459_ = lean_ctor_get(v___x_1457_, 0);
v_atomsAssignmentExprCache_1460_ = lean_ctor_get(v___x_1457_, 1);
v_atomsAssignmentMapCache_1461_ = lean_ctor_get(v___x_1457_, 2);
v_evalsAtCache_1462_ = lean_ctor_get(v___x_1457_, 3);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1464_ = v___x_1457_;
v_isShared_1465_ = v_isSharedCheck_1509_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_theoryState_1458_);
lean_inc(v_evalsAtCache_1462_);
lean_inc(v_atomsAssignmentMapCache_1461_);
lean_inc(v_atomsAssignmentExprCache_1460_);
lean_inc(v_atoms_1459_);
lean_dec(v___x_1457_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1509_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_atoms_1466_; lean_object* v_masks_1467_; lean_object* v_patterns_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1508_; 
v_atoms_1466_ = lean_ctor_get(v_theoryState_1458_, 0);
v_masks_1467_ = lean_ctor_get(v_theoryState_1458_, 1);
v_patterns_1468_ = lean_ctor_get(v_theoryState_1458_, 2);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_theoryState_1458_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1470_ = v_theoryState_1458_;
v_isShared_1471_ = v_isSharedCheck_1508_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_patterns_1468_);
lean_inc(v_masks_1467_);
lean_inc(v_atoms_1466_);
lean_dec(v_theoryState_1458_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1508_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_inc_ref(v_fst_1352_);
v___x_1472_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1472_, 0, v_fst_1352_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*1, v_snd_1353_);
v___x_1473_ = lean_array_push(v_atoms_1466_, v___x_1472_);
lean_inc_ref(v___x_1412_);
v___x_1474_ = lean_array_push(v_masks_1467_, v___x_1412_);
v___x_1475_ = lean_array_push(v_patterns_1468_, v_a_1456_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 2, v___x_1475_);
lean_ctor_set(v___x_1470_, 1, v___x_1474_);
lean_ctor_set(v___x_1470_, 0, v___x_1473_);
v___x_1477_ = v___x_1470_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___x_1477_);
v___x_1479_ = v___x_1464_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_atoms_1459_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_atomsAssignmentExprCache_1460_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_atomsAssignmentMapCache_1461_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_evalsAtCache_1462_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v_toCold_1481_; lean_object* v_options_1482_; uint8_t v_hasTrace_1483_; 
v___x_1480_ = lean_st_ref_put(v___y_1359_, v___x_1479_);
v_toCold_1481_ = lean_ctor_get(v___y_1367_, 0);
v_options_1482_ = lean_ctor_get(v_toCold_1481_, 2);
v_hasTrace_1483_ = lean_ctor_get_uint8(v_options_1482_, sizeof(void*)*1);
if (v_hasTrace_1483_ == 0)
{
lean_dec_ref(v_fst_1352_);
v___y_1414_ = v___y_1357_;
v___y_1415_ = v___y_1358_;
v___y_1416_ = v___y_1359_;
v___y_1417_ = v___y_1360_;
v___y_1418_ = v___y_1361_;
v___y_1419_ = v___y_1362_;
v___y_1420_ = v___y_1363_;
v___y_1421_ = v___y_1364_;
v___y_1422_ = v___y_1365_;
v___y_1423_ = v___y_1366_;
v___y_1424_ = v___y_1367_;
v___y_1425_ = v___y_1368_;
goto v___jp_1413_;
}
else
{
lean_object* v_inheritedTraceOptions_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_inheritedTraceOptions_1484_ = lean_ctor_get(v_toCold_1481_, 11);
v___x_1485_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6);
v___x_1486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1484_, v_options_1482_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec_ref(v_fst_1352_);
v___y_1414_ = v___y_1357_;
v___y_1415_ = v___y_1358_;
v___y_1416_ = v___y_1359_;
v___y_1417_ = v___y_1360_;
v___y_1418_ = v___y_1361_;
v___y_1419_ = v___y_1362_;
v___y_1420_ = v___y_1363_;
v___y_1421_ = v___y_1364_;
v___y_1422_ = v___y_1365_;
v___y_1423_ = v___y_1366_;
v___y_1424_ = v___y_1367_;
v___y_1425_ = v___y_1368_;
goto v___jp_1413_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1487_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__8);
v___x_1488_ = l_Lean_MessageData_ofExpr(v_fst_1352_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__10, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__10);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
lean_inc_ref(v___x_1412_);
v___x_1492_ = lean_array_to_list(v___x_1412_);
v___x_1493_ = lean_box(0);
v___x_1494_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__4(v___x_1492_, v___x_1493_);
v___x_1495_ = l_Lean_MessageData_ofList(v___x_1494_);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1491_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg(v___x_1379_, v___x_1496_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref_known(v___x_1497_, 1);
v___y_1414_ = v___y_1357_;
v___y_1415_ = v___y_1358_;
v___y_1416_ = v___y_1359_;
v___y_1417_ = v___y_1360_;
v___y_1418_ = v___y_1361_;
v___y_1419_ = v___y_1362_;
v___y_1420_ = v___y_1363_;
v___y_1421_ = v___y_1364_;
v___y_1422_ = v___y_1365_;
v___y_1423_ = v___y_1366_;
v___y_1424_ = v___y_1367_;
v___y_1425_ = v___y_1368_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_x_1355_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
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
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___x_1412_);
lean_del_object(v___x_1408_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_fst_1352_);
v_a_1510_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1455_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1455_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
}
v___jp_1413_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1426_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0));
v___x_1427_ = lean_array_get_size(v___x_1412_);
v___x_1428_ = l_Array_toSubarray___redArg(v___x_1412_, v___x_1377_, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1426_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___redArg(v_x_1355_, v_sz_1380_, v___x_1381_, v___x_1429_);
lean_dec_ref(v_x_1355_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1442_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1442_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1442_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_fst_1435_; lean_object* v___x_1437_; 
v_fst_1435_ = lean_ctor_get(v_a_1431_, 0);
lean_inc(v_fst_1435_);
lean_dec(v_a_1431_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v_fst_1435_);
v___x_1437_ = v___x_1408_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_fst_1435_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1437_);
v___x_1439_ = v___x_1433_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_del_object(v___x_1408_);
v_a_1443_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1430_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1430_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_del_object(v___x_1399_);
lean_dec(v_a_1397_);
lean_dec(v_a_1383_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_fst_1352_);
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
v___jp_1401_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_a_1383_);
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_fst_1352_);
v_a_1522_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1396_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1396_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
v___jp_1387_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = lean_box(0);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1388_);
v___x_1390_ = v___x_1385_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_x_1354_);
lean_dec_ref(v_fst_1352_);
v_a_1531_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1382_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1382_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec_ref(v_x_1355_);
lean_dec_ref(v_x_1354_);
lean_dec_ref(v_fst_1352_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___boxed(lean_object** _args){
lean_object* v___x_1541_ = _args[0];
lean_object* v_fst_1542_ = _args[1];
lean_object* v_snd_1543_ = _args[2];
lean_object* v_x_1544_ = _args[3];
lean_object* v_x_1545_ = _args[4];
lean_object* v_x_1546_ = _args[5];
lean_object* v___y_1547_ = _args[6];
lean_object* v___y_1548_ = _args[7];
lean_object* v___y_1549_ = _args[8];
lean_object* v___y_1550_ = _args[9];
lean_object* v___y_1551_ = _args[10];
lean_object* v___y_1552_ = _args[11];
lean_object* v___y_1553_ = _args[12];
lean_object* v___y_1554_ = _args[13];
lean_object* v___y_1555_ = _args[14];
lean_object* v___y_1556_ = _args[15];
lean_object* v___y_1557_ = _args[16];
lean_object* v___y_1558_ = _args[17];
lean_object* v___y_1559_ = _args[18];
_start:
{
uint8_t v___x_94308__boxed_1560_; uint8_t v_snd_94310__boxed_1561_; lean_object* v_res_1562_; 
v___x_94308__boxed_1560_ = lean_unbox(v___x_1541_);
v_snd_94310__boxed_1561_ = lean_unbox(v_snd_1543_);
v_res_1562_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6(v___x_94308__boxed_1560_, v_fst_1542_, v_snd_94310__boxed_1561_, v_x_1544_, v_x_1545_, v_x_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
return v_res_1562_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__1(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__0));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom(lean_object* v_e_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_config_1580_; uint8_t v_uf_1581_; 
v_config_1580_ = lean_ctor_get(v_a_1568_, 1);
v_uf_1581_ = lean_ctor_get_uint8(v_config_1580_, sizeof(void*)*3 + 11);
if (v_uf_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec_ref(v_e_1566_);
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_unwrapBoolAtom___redArg(v_e_1566_, v_a_1576_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1632_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v_fst_1586_ = lean_ctor_get(v_a_1585_, 0);
v_snd_1587_ = lean_ctor_get(v_a_1585_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_a_1585_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1589_ = v_a_1585_;
v_isShared_1590_ = v_isSharedCheck_1632_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_snd_1587_);
lean_inc(v_fst_1586_);
lean_dec(v_a_1585_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1632_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v_toCold_1611_; lean_object* v_options_1612_; uint8_t v_hasTrace_1613_; 
v_toCold_1611_ = lean_ctor_get(v_a_1577_, 0);
v_options_1612_ = lean_ctor_get(v_toCold_1611_, 2);
v_hasTrace_1613_ = lean_ctor_get_uint8(v_options_1612_, sizeof(void*)*1);
if (v_hasTrace_1613_ == 0)
{
lean_del_object(v___x_1589_);
v___y_1592_ = v_a_1567_;
v___y_1593_ = v_a_1568_;
v___y_1594_ = v_a_1569_;
v___y_1595_ = v_a_1570_;
v___y_1596_ = v_a_1571_;
v___y_1597_ = v_a_1572_;
v___y_1598_ = v_a_1573_;
v___y_1599_ = v_a_1574_;
v___y_1600_ = v_a_1575_;
v___y_1601_ = v_a_1576_;
v___y_1602_ = v_a_1577_;
v___y_1603_ = v_a_1578_;
goto v___jp_1591_;
}
else
{
lean_object* v_inheritedTraceOptions_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_inheritedTraceOptions_1614_ = lean_ctor_get(v_toCold_1611_, 11);
v___x_1615_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__3));
v___x_1616_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__6);
v___x_1617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1614_, v_options_1612_, v___x_1616_);
if (v___x_1617_ == 0)
{
lean_del_object(v___x_1589_);
v___y_1592_ = v_a_1567_;
v___y_1593_ = v_a_1568_;
v___y_1594_ = v_a_1569_;
v___y_1595_ = v_a_1570_;
v___y_1596_ = v_a_1571_;
v___y_1597_ = v_a_1572_;
v___y_1598_ = v_a_1573_;
v___y_1599_ = v_a_1574_;
v___y_1600_ = v_a_1575_;
v___y_1601_ = v_a_1576_;
v___y_1602_ = v_a_1577_;
v___y_1603_ = v_a_1578_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___closed__1);
lean_inc(v_fst_1586_);
v___x_1619_ = l_Lean_MessageData_ofExpr(v_fst_1586_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 7);
lean_ctor_set(v___x_1589_, 1, v___x_1619_);
lean_ctor_set(v___x_1589_, 0, v___x_1618_);
v___x_1621_ = v___x_1589_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg(v___x_1615_, v___x_1621_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_dec_ref_known(v___x_1622_, 1);
v___y_1592_ = v_a_1567_;
v___y_1593_ = v_a_1568_;
v___y_1594_ = v_a_1569_;
v___y_1595_ = v_a_1570_;
v___y_1596_ = v_a_1571_;
v___y_1597_ = v_a_1572_;
v___y_1598_ = v_a_1573_;
v___y_1599_ = v_a_1574_;
v___y_1600_ = v_a_1575_;
v___y_1601_ = v_a_1576_;
v___y_1602_ = v_a_1577_;
v___y_1603_ = v_a_1578_;
goto v___jp_1591_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
v___jp_1591_:
{
lean_object* v_dummy_1604_; lean_object* v_nargs_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; 
v_dummy_1604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern___closed__0);
v_nargs_1605_ = l_Lean_Expr_getAppNumArgs(v_fst_1586_);
lean_inc(v_nargs_1605_);
v___x_1606_ = lean_mk_array(v_nargs_1605_, v_dummy_1604_);
v___x_1607_ = lean_unsigned_to_nat(1u);
v___x_1608_ = lean_nat_sub(v_nargs_1605_, v___x_1607_);
lean_dec(v_nargs_1605_);
v___x_1609_ = lean_unbox(v_snd_1587_);
lean_dec(v_snd_1587_);
lean_inc(v_fst_1586_);
v___x_1610_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6(v_uf_1581_, v_fst_1586_, v___x_1609_, v_fst_1586_, v___x_1606_, v___x_1608_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
return v___x_1610_;
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_a_1633_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1584_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1584_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom___boxed(lean_object* v_e_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom(v_e_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0(uint8_t v___x_1656_, size_t v_sz_1657_, size_t v_i_1658_, lean_object* v_bs_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___redArg(v___x_1656_, v_sz_1657_, v_i_1658_, v_bs_1659_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0___boxed(lean_object** _args){
lean_object* v___x_1674_ = _args[0];
lean_object* v_sz_1675_ = _args[1];
lean_object* v_i_1676_ = _args[2];
lean_object* v_bs_1677_ = _args[3];
lean_object* v___y_1678_ = _args[4];
lean_object* v___y_1679_ = _args[5];
lean_object* v___y_1680_ = _args[6];
lean_object* v___y_1681_ = _args[7];
lean_object* v___y_1682_ = _args[8];
lean_object* v___y_1683_ = _args[9];
lean_object* v___y_1684_ = _args[10];
lean_object* v___y_1685_ = _args[11];
lean_object* v___y_1686_ = _args[12];
lean_object* v___y_1687_ = _args[13];
lean_object* v___y_1688_ = _args[14];
lean_object* v___y_1689_ = _args[15];
lean_object* v___y_1690_ = _args[16];
_start:
{
uint8_t v___x_94830__boxed_1691_; size_t v_sz_boxed_1692_; size_t v_i_boxed_1693_; lean_object* v_res_1694_; 
v___x_94830__boxed_1691_ = lean_unbox(v___x_1674_);
v_sz_boxed_1692_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1693_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__0(v___x_94830__boxed_1691_, v_sz_boxed_1692_, v_i_boxed_1693_, v_bs_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3(lean_object* v_as_1695_, size_t v_sz_1696_, size_t v_i_1697_, lean_object* v_b_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___redArg(v_as_1695_, v_sz_1696_, v_i_1697_, v_b_1698_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3___boxed(lean_object** _args){
lean_object* v_as_1713_ = _args[0];
lean_object* v_sz_1714_ = _args[1];
lean_object* v_i_1715_ = _args[2];
lean_object* v_b_1716_ = _args[3];
lean_object* v___y_1717_ = _args[4];
lean_object* v___y_1718_ = _args[5];
lean_object* v___y_1719_ = _args[6];
lean_object* v___y_1720_ = _args[7];
lean_object* v___y_1721_ = _args[8];
lean_object* v___y_1722_ = _args[9];
lean_object* v___y_1723_ = _args[10];
lean_object* v___y_1724_ = _args[11];
lean_object* v___y_1725_ = _args[12];
lean_object* v___y_1726_ = _args[13];
lean_object* v___y_1727_ = _args[14];
lean_object* v___y_1728_ = _args[15];
lean_object* v___y_1729_ = _args[16];
_start:
{
size_t v_sz_boxed_1730_; size_t v_i_boxed_1731_; lean_object* v_res_1732_; 
v_sz_boxed_1730_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1731_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__3(v_as_1713_, v_sz_boxed_1730_, v_i_boxed_1731_, v_b_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v_as_1713_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5(lean_object* v_cls_1733_, lean_object* v_msg_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___redArg(v_cls_1733_, v_msg_1734_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5___boxed(lean_object* v_cls_1749_, lean_object* v_msg_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5(v_cls_1749_, v_msg_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object* v___x_1765_, lean_object* v_fst_1766_, lean_object* v_fproof_1767_, lean_object* v_snd_1768_, lean_object* v_sproof_1769_){
_start:
{
if (lean_obj_tag(v_fproof_1767_) == 0)
{
lean_dec_ref(v_snd_1768_);
if (lean_obj_tag(v_sproof_1769_) == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref(v_fst_1766_);
lean_dec(v___x_1765_);
v___x_1770_ = lean_box(0);
return v___x_1770_;
}
else
{
lean_object* v_val_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1780_; 
v_val_1771_ = lean_ctor_get(v_sproof_1769_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_sproof_1769_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1773_ = v_sproof_1769_;
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_val_1771_);
lean_dec(v_sproof_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1775_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_1765_, v_fst_1766_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v_val_1771_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1776_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_dec_ref(v_fst_1766_);
if (lean_obj_tag(v_sproof_1769_) == 0)
{
lean_object* v_val_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1790_; 
v_val_1781_ = lean_ctor_get(v_fproof_1767_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_fproof_1767_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1783_ = v_fproof_1767_;
v_isShared_1784_ = v_isSharedCheck_1790_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_val_1781_);
lean_dec(v_fproof_1767_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1790_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_1765_, v_snd_1768_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_val_1781_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1786_);
v___x_1788_ = v___x_1783_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v_val_1791_; lean_object* v_val_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v_snd_1768_);
lean_dec(v___x_1765_);
v_val_1791_ = lean_ctor_get(v_fproof_1767_, 0);
lean_inc(v_val_1791_);
lean_dec_ref_known(v_fproof_1767_, 1);
v_val_1792_ = lean_ctor_get(v_sproof_1769_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_sproof_1769_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1794_ = v_sproof_1769_;
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_val_1792_);
lean_dec(v_sproof_1769_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_val_1791_);
lean_ctor_set(v___x_1796_, 1, v_val_1792_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1796_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(lean_object* v_lhs_1801_, lean_object* v_rhs_1802_, lean_object* v_lhsExpr_1803_, lean_object* v_rhsExpr_1804_, lean_object* v_congrThm_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_width_1818_; lean_object* v_expr_1819_; lean_object* v___x_1820_; 
v_width_1818_ = lean_ctor_get(v_lhs_1801_, 0);
lean_inc_n(v_width_1818_, 2);
v_expr_1819_ = lean_ctor_get(v_lhs_1801_, 4);
lean_inc_ref(v_expr_1819_);
v___x_1820_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_1818_, v_expr_1819_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v_width_1822_; lean_object* v_expr_1823_; lean_object* v___x_1824_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v_width_1822_ = lean_ctor_get(v_rhs_1802_, 0);
v_expr_1823_ = lean_ctor_get(v_rhs_1802_, 4);
lean_inc_ref(v_expr_1823_);
lean_inc(v_width_1822_);
v___x_1824_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_1822_, v_expr_1823_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_lhs_1801_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_rhs_1802_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1852_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1852_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1852_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; 
lean_inc(v_a_1825_);
lean_inc(v_a_1821_);
v___x_1833_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(v_width_1818_, v_a_1821_, v_a_1827_, v_a_1825_, v_a_1829_);
if (lean_obj_tag(v___x_1833_) == 1)
{
lean_object* v_val_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1847_; 
v_val_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1847_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_val_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1847_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_fst_1838_; lean_object* v_snd_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
v_fst_1838_ = lean_ctor_get(v_val_1834_, 0);
lean_inc(v_fst_1838_);
v_snd_1839_ = lean_ctor_get(v_val_1834_, 1);
lean_inc(v_snd_1839_);
lean_dec(v_val_1834_);
v___x_1840_ = l_Lean_mkApp6(v_congrThm_1805_, v_lhsExpr_1803_, v_rhsExpr_1804_, v_a_1821_, v_a_1825_, v_fst_1838_, v_snd_1839_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1840_);
v___x_1842_ = v___x_1836_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1842_);
v___x_1844_ = v___x_1831_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v___x_1833_);
lean_dec(v_a_1825_);
lean_dec(v_a_1821_);
lean_dec_ref(v_congrThm_1805_);
lean_dec_ref(v_rhsExpr_1804_);
lean_dec_ref(v_lhsExpr_1803_);
v___x_1848_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1848_);
v___x_1850_ = v___x_1831_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_dec(v_a_1827_);
lean_dec(v_a_1825_);
lean_dec(v_a_1821_);
lean_dec(v_width_1818_);
lean_dec_ref(v_congrThm_1805_);
lean_dec_ref(v_rhsExpr_1804_);
lean_dec_ref(v_lhsExpr_1803_);
return v___x_1828_;
}
}
else
{
lean_dec(v_a_1825_);
lean_dec(v_a_1821_);
lean_dec(v_width_1818_);
lean_dec_ref(v_congrThm_1805_);
lean_dec_ref(v_rhsExpr_1804_);
lean_dec_ref(v_lhsExpr_1803_);
lean_dec_ref(v_rhs_1802_);
return v___x_1826_;
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec(v_a_1821_);
lean_dec(v_width_1818_);
lean_dec_ref(v_congrThm_1805_);
lean_dec_ref(v_rhsExpr_1804_);
lean_dec_ref(v_lhsExpr_1803_);
lean_dec_ref(v_rhs_1802_);
lean_dec_ref(v_lhs_1801_);
v_a_1853_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1824_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1824_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_width_1818_);
lean_dec_ref(v_congrThm_1805_);
lean_dec_ref(v_rhsExpr_1804_);
lean_dec_ref(v_lhsExpr_1803_);
lean_dec_ref(v_rhs_1802_);
lean_dec_ref(v_lhs_1801_);
v_a_1861_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1820_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1820_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object** _args){
lean_object* v_lhs_1869_ = _args[0];
lean_object* v_rhs_1870_ = _args[1];
lean_object* v_lhsExpr_1871_ = _args[2];
lean_object* v_rhsExpr_1872_ = _args[3];
lean_object* v_congrThm_1873_ = _args[4];
lean_object* v_a_1874_ = _args[5];
lean_object* v_a_1875_ = _args[6];
lean_object* v_a_1876_ = _args[7];
lean_object* v_a_1877_ = _args[8];
lean_object* v_a_1878_ = _args[9];
lean_object* v_a_1879_ = _args[10];
lean_object* v_a_1880_ = _args[11];
lean_object* v_a_1881_ = _args[12];
lean_object* v_a_1882_ = _args[13];
lean_object* v_a_1883_ = _args[14];
lean_object* v_a_1884_ = _args[15];
lean_object* v_a_1885_ = _args[16];
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(v_lhs_1869_, v_rhs_1870_, v_lhsExpr_1871_, v_rhsExpr_1872_, v_congrThm_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(lean_object* v_inner_1887_, lean_object* v_innerExpr_1888_, lean_object* v_congrProof_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_width_1902_; lean_object* v_expr_1903_; lean_object* v___x_1904_; 
v_width_1902_ = lean_ctor_get(v_inner_1887_, 0);
lean_inc_n(v_width_1902_, 2);
v_expr_1903_ = lean_ctor_get(v_inner_1887_, 4);
lean_inc_ref(v_expr_1903_);
v___x_1904_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_1902_, v_expr_1903_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_inner_1887_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1928_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1928_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
if (lean_obj_tag(v_a_1907_) == 1)
{
lean_object* v_val_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1923_; 
v_val_1911_ = lean_ctor_get(v_a_1907_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_a_1907_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1913_ = v_a_1907_;
v_isShared_1914_ = v_isSharedCheck_1923_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_val_1911_);
lean_dec(v_a_1907_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1923_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1915_ = l_Lean_mkNatLit(v_width_1902_);
v___x_1916_ = l_Lean_mkApp4(v_congrProof_1889_, v___x_1915_, v_innerExpr_1888_, v_a_1905_, v_val_1911_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1916_);
v___x_1918_ = v___x_1913_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1918_);
v___x_1920_ = v___x_1909_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_dec(v_a_1907_);
lean_dec(v_a_1905_);
lean_dec(v_width_1902_);
lean_dec_ref(v_congrProof_1889_);
lean_dec_ref(v_innerExpr_1888_);
v___x_1924_ = lean_box(0);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1924_);
v___x_1926_ = v___x_1909_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_dec(v_a_1905_);
lean_dec(v_width_1902_);
lean_dec_ref(v_congrProof_1889_);
lean_dec_ref(v_innerExpr_1888_);
return v___x_1906_;
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_width_1902_);
lean_dec_ref(v_congrProof_1889_);
lean_dec_ref(v_innerExpr_1888_);
lean_dec_ref(v_inner_1887_);
v_a_1929_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1904_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1904_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object* v_inner_1937_, lean_object* v_innerExpr_1938_, lean_object* v_congrProof_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(v_inner_1937_, v_innerExpr_1938_, v_congrProof_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_checkTheoryAtom(uint8_t v_synthetic_1953_, lean_object* v_e_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
if (v_synthetic_1953_ == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v_e_1954_, v_a_1957_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2000_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_2000_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2000_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_unbox(v_a_1969_);
lean_dec(v_a_1969_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_del_object(v___x_1971_);
v___x_1974_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom(v_e_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1987_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1987_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1987_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
if (lean_obj_tag(v_a_1975_) == 1)
{
lean_object* v_val_1979_; lean_object* v___x_1981_; 
v_val_1979_ = lean_ctor_get(v_a_1975_, 0);
lean_inc(v_val_1979_);
lean_dec_ref_known(v_a_1975_, 1);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_val_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_val_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec(v_a_1975_);
v___x_1983_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0));
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1983_);
v___x_1985_ = v___x_1977_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1974_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1974_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
lean_dec_ref(v_e_1954_);
v___x_1996_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0));
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1996_);
v___x_1998_ = v___x_1971_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_e_1954_);
v_a_2001_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1968_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1968_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec_ref(v_e_1954_);
v___x_2009_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_getFunctionPattern_spec__3_spec__4_spec__6___closed__0));
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_checkTheoryAtom___boxed(lean_object* v_synthetic_2011_, lean_object* v_e_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
uint8_t v_synthetic_boxed_2026_; lean_object* v_res_2027_; 
v_synthetic_boxed_2026_ = lean_unbox(v_synthetic_2011_);
v_res_2027_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_checkTheoryAtom(v_synthetic_boxed_2026_, v_e_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__26___redArg(lean_object* v_a_2028_, lean_object* v_b_2029_, lean_object* v_x_2030_){
_start:
{
if (lean_obj_tag(v_x_2030_) == 0)
{
lean_dec(v_b_2029_);
lean_dec_ref(v_a_2028_);
return v_x_2030_;
}
else
{
lean_object* v_key_2031_; lean_object* v_value_2032_; lean_object* v_tail_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2047_; 
v_key_2031_ = lean_ctor_get(v_x_2030_, 0);
v_value_2032_ = lean_ctor_get(v_x_2030_, 1);
v_tail_2033_ = lean_ctor_get(v_x_2030_, 2);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_x_2030_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2035_ = v_x_2030_;
v_isShared_2036_ = v_isSharedCheck_2047_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_tail_2033_);
lean_inc(v_value_2032_);
lean_inc(v_key_2031_);
lean_dec(v_x_2030_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2047_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
size_t v___x_2037_; size_t v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = lean_ptr_addr(v_key_2031_);
v___x_2038_ = lean_ptr_addr(v_a_2028_);
v___x_2039_ = lean_usize_dec_eq(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__26___redArg(v_a_2028_, v_b_2029_, v_tail_2033_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 2, v___x_2040_);
v___x_2042_ = v___x_2035_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_key_2031_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_value_2032_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
else
{
lean_object* v___x_2045_; 
lean_dec(v_value_2032_);
lean_dec(v_key_2031_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_b_2029_);
lean_ctor_set(v___x_2035_, 0, v_a_2028_);
v___x_2045_ = v___x_2035_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2028_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_b_2029_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_tail_2033_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30_spec__31___redArg(lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
return v_x_2048_;
}
else
{
lean_object* v_key_2050_; lean_object* v_value_2051_; lean_object* v_tail_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2078_; 
v_key_2050_ = lean_ctor_get(v_x_2049_, 0);
v_value_2051_ = lean_ctor_get(v_x_2049_, 1);
v_tail_2052_ = lean_ctor_get(v_x_2049_, 2);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_x_2049_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2054_ = v_x_2049_;
v_isShared_2055_ = v_isSharedCheck_2078_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_tail_2052_);
lean_inc(v_value_2051_);
lean_inc(v_key_2050_);
lean_dec(v_x_2049_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2078_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint64_t v___x_2062_; uint64_t v_fold_2063_; uint64_t v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; size_t v___x_2067_; size_t v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2056_ = lean_array_get_size(v_x_2048_);
v___x_2057_ = lean_ptr_addr(v_key_2050_);
v___x_2058_ = ((size_t)3ULL);
v___x_2059_ = lean_usize_shift_right(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_usize_to_uint64(v___x_2059_);
v___x_2061_ = 32ULL;
v___x_2062_ = lean_uint64_shift_right(v___x_2060_, v___x_2061_);
v_fold_2063_ = lean_uint64_xor(v___x_2060_, v___x_2062_);
v___x_2064_ = 16ULL;
v___x_2065_ = lean_uint64_shift_right(v_fold_2063_, v___x_2064_);
v___x_2066_ = lean_uint64_xor(v_fold_2063_, v___x_2065_);
v___x_2067_ = lean_uint64_to_usize(v___x_2066_);
v___x_2068_ = lean_usize_of_nat(v___x_2056_);
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_sub(v___x_2068_, v___x_2069_);
v___x_2071_ = lean_usize_land(v___x_2067_, v___x_2070_);
v___x_2072_ = lean_array_uget_borrowed(v_x_2048_, v___x_2071_);
lean_inc(v___x_2072_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 2, v___x_2072_);
v___x_2074_ = v___x_2054_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_key_2050_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_value_2051_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_array_uset(v_x_2048_, v___x_2071_, v___x_2074_);
v_x_2048_ = v___x_2075_;
v_x_2049_ = v_tail_2052_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30___redArg(lean_object* v_i_2079_, lean_object* v_source_2080_, lean_object* v_target_2081_){
_start:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = lean_array_get_size(v_source_2080_);
v___x_2083_ = lean_nat_dec_lt(v_i_2079_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v_source_2080_);
lean_dec(v_i_2079_);
return v_target_2081_;
}
else
{
lean_object* v_es_2084_; lean_object* v___x_2085_; lean_object* v_source_2086_; lean_object* v_target_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_es_2084_ = lean_array_fget(v_source_2080_, v_i_2079_);
v___x_2085_ = lean_box(0);
v_source_2086_ = lean_array_fset(v_source_2080_, v_i_2079_, v___x_2085_);
v_target_2087_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30_spec__31___redArg(v_target_2081_, v_es_2084_);
v___x_2088_ = lean_unsigned_to_nat(1u);
v___x_2089_ = lean_nat_add(v_i_2079_, v___x_2088_);
lean_dec(v_i_2079_);
v_i_2079_ = v___x_2089_;
v_source_2080_ = v_source_2086_;
v_target_2081_ = v_target_2087_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25___redArg(lean_object* v_data_2091_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_nbuckets_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2092_ = lean_array_get_size(v_data_2091_);
v___x_2093_ = lean_unsigned_to_nat(2u);
v_nbuckets_2094_ = lean_nat_mul(v___x_2092_, v___x_2093_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_mk_array(v_nbuckets_2094_, v___x_2096_);
v___x_2098_ = lean_array_propagate_mark(v_data_2091_, v___x_2097_);
v___x_2099_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30___redArg(v___x_2095_, v_data_2091_, v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___redArg(lean_object* v_a_2100_, lean_object* v_x_2101_){
_start:
{
if (lean_obj_tag(v_x_2101_) == 0)
{
uint8_t v___x_2102_; 
v___x_2102_ = 0;
return v___x_2102_;
}
else
{
lean_object* v_key_2103_; lean_object* v_tail_2104_; size_t v___x_2105_; size_t v___x_2106_; uint8_t v___x_2107_; 
v_key_2103_ = lean_ctor_get(v_x_2101_, 0);
v_tail_2104_ = lean_ctor_get(v_x_2101_, 2);
v___x_2105_ = lean_ptr_addr(v_key_2103_);
v___x_2106_ = lean_ptr_addr(v_a_2100_);
v___x_2107_ = lean_usize_dec_eq(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
v_x_2101_ = v_tail_2104_;
goto _start;
}
else
{
return v___x_2107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___redArg___boxed(lean_object* v_a_2109_, lean_object* v_x_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___redArg(v_a_2109_, v_x_2110_);
lean_dec(v_x_2110_);
lean_dec_ref(v_a_2109_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17___redArg(lean_object* v_m_2113_, lean_object* v_a_2114_, lean_object* v_b_2115_){
_start:
{
lean_object* v_size_2116_; lean_object* v_buckets_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2163_; 
v_size_2116_ = lean_ctor_get(v_m_2113_, 0);
v_buckets_2117_ = lean_ctor_get(v_m_2113_, 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_m_2113_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2119_ = v_m_2113_;
v_isShared_2120_ = v_isSharedCheck_2163_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_buckets_2117_);
lean_inc(v_size_2116_);
lean_dec(v_m_2113_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2163_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; size_t v___x_2122_; size_t v___x_2123_; size_t v___x_2124_; uint64_t v___x_2125_; uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v_fold_2128_; uint64_t v___x_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; lean_object* v_bkt_2137_; uint8_t v___x_2138_; 
v___x_2121_ = lean_array_get_size(v_buckets_2117_);
v___x_2122_ = lean_ptr_addr(v_a_2114_);
v___x_2123_ = ((size_t)3ULL);
v___x_2124_ = lean_usize_shift_right(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_usize_to_uint64(v___x_2124_);
v___x_2126_ = 32ULL;
v___x_2127_ = lean_uint64_shift_right(v___x_2125_, v___x_2126_);
v_fold_2128_ = lean_uint64_xor(v___x_2125_, v___x_2127_);
v___x_2129_ = 16ULL;
v___x_2130_ = lean_uint64_shift_right(v_fold_2128_, v___x_2129_);
v___x_2131_ = lean_uint64_xor(v_fold_2128_, v___x_2130_);
v___x_2132_ = lean_uint64_to_usize(v___x_2131_);
v___x_2133_ = lean_usize_of_nat(v___x_2121_);
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_sub(v___x_2133_, v___x_2134_);
v___x_2136_ = lean_usize_land(v___x_2132_, v___x_2135_);
v_bkt_2137_ = lean_array_uget_borrowed(v_buckets_2117_, v___x_2136_);
v___x_2138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___redArg(v_a_2114_, v_bkt_2137_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v_size_x27_2140_; lean_object* v___x_2141_; lean_object* v_buckets_x27_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2139_ = lean_unsigned_to_nat(1u);
v_size_x27_2140_ = lean_nat_add(v_size_2116_, v___x_2139_);
lean_dec(v_size_2116_);
lean_inc(v_bkt_2137_);
v___x_2141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2141_, 0, v_a_2114_);
lean_ctor_set(v___x_2141_, 1, v_b_2115_);
lean_ctor_set(v___x_2141_, 2, v_bkt_2137_);
v_buckets_x27_2142_ = lean_array_uset(v_buckets_2117_, v___x_2136_, v___x_2141_);
v___x_2143_ = lean_unsigned_to_nat(4u);
v___x_2144_ = lean_nat_mul(v_size_x27_2140_, v___x_2143_);
v___x_2145_ = lean_unsigned_to_nat(3u);
v___x_2146_ = lean_nat_div(v___x_2144_, v___x_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_array_get_size(v_buckets_x27_2142_);
v___x_2148_ = lean_nat_dec_le(v___x_2146_, v___x_2147_);
lean_dec(v___x_2146_);
if (v___x_2148_ == 0)
{
lean_object* v_val_2149_; lean_object* v___x_2151_; 
v_val_2149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25___redArg(v_buckets_x27_2142_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_val_2149_);
lean_ctor_set(v___x_2119_, 0, v_size_x27_2140_);
v___x_2151_ = v___x_2119_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_size_x27_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_val_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
else
{
lean_object* v___x_2154_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v_buckets_x27_2142_);
lean_ctor_set(v___x_2119_, 0, v_size_x27_2140_);
v___x_2154_ = v___x_2119_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_size_x27_2140_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_buckets_x27_2142_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
else
{
lean_object* v___x_2156_; lean_object* v_buckets_x27_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_inc(v_bkt_2137_);
v___x_2156_ = lean_box(0);
v_buckets_x27_2157_ = lean_array_uset(v_buckets_2117_, v___x_2136_, v___x_2156_);
v___x_2158_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__26___redArg(v_a_2114_, v_b_2115_, v_bkt_2137_);
v___x_2159_ = lean_array_uset(v_buckets_x27_2157_, v___x_2136_, v___x_2158_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v___x_2159_);
v___x_2161_ = v___x_2119_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_size_2116_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0(lean_object* v_n_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_n_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(lean_object* v_width_2168_, lean_object* v_expr_2169_, lean_object* v_val_2170_, lean_object* v___x_2171_, lean_object* v___x_2172_, lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v___x_2175_, lean_object* v_arg_2176_, lean_object* v_arg_2177_, lean_object* v___x_2178_, lean_object* v_arg_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_2168_, v_expr_2169_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_2170_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2219_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2219_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2219_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_val_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2214_; 
v_val_2199_ = lean_ctor_get(v_a_2195_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_a_2195_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2201_ = v_a_2195_;
v_isShared_2202_ = v_isSharedCheck_2214_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_val_2199_);
lean_dec(v_a_2195_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2214_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0));
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1));
v___x_2205_ = l_Lean_Name_mkStr6(v___x_2171_, v___x_2172_, v___x_2173_, v___x_2203_, v___x_2174_, v___x_2204_);
v___x_2206_ = l_Lean_mkConst(v___x_2205_, v___x_2175_);
v___x_2207_ = l_Lean_mkApp6(v___x_2206_, v_arg_2176_, v_arg_2177_, v___x_2178_, v_arg_2179_, v_a_2193_, v_val_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2207_);
v___x_2209_ = v___x_2201_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2211_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2209_);
v___x_2211_ = v___x_2197_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec(v_a_2195_);
lean_dec(v_a_2193_);
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v___x_2178_);
lean_dec_ref(v_arg_2177_);
lean_dec_ref(v_arg_2176_);
lean_dec(v___x_2175_);
lean_dec_ref(v___x_2174_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec_ref(v___x_2171_);
v___x_2215_ = lean_box(0);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2215_);
v___x_2217_ = v___x_2197_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_dec(v_a_2193_);
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v___x_2178_);
lean_dec_ref(v_arg_2177_);
lean_dec_ref(v_arg_2176_);
lean_dec(v___x_2175_);
lean_dec_ref(v___x_2174_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec_ref(v___x_2171_);
return v___x_2194_;
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref(v_arg_2179_);
lean_dec_ref(v___x_2178_);
lean_dec_ref(v_arg_2177_);
lean_dec_ref(v_arg_2176_);
lean_dec(v___x_2175_);
lean_dec_ref(v___x_2174_);
lean_dec_ref(v___x_2173_);
lean_dec_ref(v___x_2172_);
lean_dec_ref(v___x_2171_);
lean_dec_ref(v_val_2170_);
v_a_2220_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2192_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2192_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___boxed(lean_object** _args){
lean_object* v_width_2228_ = _args[0];
lean_object* v_expr_2229_ = _args[1];
lean_object* v_val_2230_ = _args[2];
lean_object* v___x_2231_ = _args[3];
lean_object* v___x_2232_ = _args[4];
lean_object* v___x_2233_ = _args[5];
lean_object* v___x_2234_ = _args[6];
lean_object* v___x_2235_ = _args[7];
lean_object* v_arg_2236_ = _args[8];
lean_object* v_arg_2237_ = _args[9];
lean_object* v___x_2238_ = _args[10];
lean_object* v_arg_2239_ = _args[11];
lean_object* v___y_2240_ = _args[12];
lean_object* v___y_2241_ = _args[13];
lean_object* v___y_2242_ = _args[14];
lean_object* v___y_2243_ = _args[15];
lean_object* v___y_2244_ = _args[16];
lean_object* v___y_2245_ = _args[17];
lean_object* v___y_2246_ = _args[18];
lean_object* v___y_2247_ = _args[19];
lean_object* v___y_2248_ = _args[20];
lean_object* v___y_2249_ = _args[21];
lean_object* v___y_2250_ = _args[22];
lean_object* v___y_2251_ = _args[23];
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(v_width_2228_, v_expr_2229_, v_val_2230_, v___x_2231_, v___x_2232_, v___x_2233_, v___x_2234_, v___x_2235_, v_arg_2236_, v_arg_2237_, v___x_2238_, v_arg_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(lean_object* v_width_2254_, lean_object* v_expr_2255_, lean_object* v_val_2256_, lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v___x_2259_, lean_object* v___x_2260_, lean_object* v___x_2261_, lean_object* v___x_2262_, lean_object* v___x_2263_, lean_object* v_arg_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_2254_, v_expr_2255_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
v___x_2279_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_2256_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2304_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2304_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2304_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
if (lean_obj_tag(v_a_2280_) == 1)
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2299_; 
v_val_2284_ = lean_ctor_get(v_a_2280_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_a_2280_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2286_ = v_a_2280_;
v_isShared_2287_ = v_isSharedCheck_2299_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v_a_2280_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2299_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0));
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0));
v___x_2290_ = l_Lean_Name_mkStr6(v___x_2257_, v___x_2258_, v___x_2259_, v___x_2288_, v___x_2260_, v___x_2289_);
v___x_2291_ = l_Lean_mkConst(v___x_2290_, v___x_2261_);
v___x_2292_ = l_Lean_mkApp5(v___x_2291_, v___x_2262_, v___x_2263_, v_arg_2264_, v_a_2278_, v_val_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2292_);
v___x_2294_ = v___x_2286_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2296_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2294_);
v___x_2296_ = v___x_2282_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_dec(v_a_2280_);
lean_dec(v_a_2278_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v___x_2262_);
lean_dec(v___x_2261_);
lean_dec_ref(v___x_2260_);
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
lean_dec_ref(v___x_2257_);
v___x_2300_ = lean_box(0);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2300_);
v___x_2302_ = v___x_2282_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_dec(v_a_2278_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v___x_2262_);
lean_dec(v___x_2261_);
lean_dec_ref(v___x_2260_);
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
lean_dec_ref(v___x_2257_);
return v___x_2279_;
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v___x_2263_);
lean_dec_ref(v___x_2262_);
lean_dec(v___x_2261_);
lean_dec_ref(v___x_2260_);
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
lean_dec_ref(v___x_2257_);
lean_dec_ref(v_val_2256_);
v_a_2305_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2277_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2277_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___boxed(lean_object** _args){
lean_object* v_width_2313_ = _args[0];
lean_object* v_expr_2314_ = _args[1];
lean_object* v_val_2315_ = _args[2];
lean_object* v___x_2316_ = _args[3];
lean_object* v___x_2317_ = _args[4];
lean_object* v___x_2318_ = _args[5];
lean_object* v___x_2319_ = _args[6];
lean_object* v___x_2320_ = _args[7];
lean_object* v___x_2321_ = _args[8];
lean_object* v___x_2322_ = _args[9];
lean_object* v_arg_2323_ = _args[10];
lean_object* v___y_2324_ = _args[11];
lean_object* v___y_2325_ = _args[12];
lean_object* v___y_2326_ = _args[13];
lean_object* v___y_2327_ = _args[14];
lean_object* v___y_2328_ = _args[15];
lean_object* v___y_2329_ = _args[16];
lean_object* v___y_2330_ = _args[17];
lean_object* v___y_2331_ = _args[18];
lean_object* v___y_2332_ = _args[19];
lean_object* v___y_2333_ = _args[20];
lean_object* v___y_2334_ = _args[21];
lean_object* v___y_2335_ = _args[22];
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(v_width_2313_, v_expr_2314_, v_val_2315_, v___x_2316_, v___x_2317_, v___x_2318_, v___x_2319_, v___x_2320_, v___x_2321_, v___x_2322_, v_arg_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg(lean_object* v_msg_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_ref_2343_; lean_object* v___x_2344_; lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2353_; 
v_ref_2343_ = lean_ctor_get(v___y_2340_, 2);
v___x_2344_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__5_spec__5(v_msg_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2353_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2353_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_inc(v_ref_2343_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v_ref_2343_);
lean_ctor_set(v___x_2349_, 1, v_a_2345_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 1);
lean_ctor_set(v___x_2347_, 0, v___x_2349_);
v___x_2351_ = v___x_2347_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg___boxed(lean_object* v_msg_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg(v_msg_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__14(lean_object* v___x_2361_, lean_object* v___x_2362_, lean_object* v_fst_2363_, lean_object* v_fproof_2364_, lean_object* v_snd_2365_, lean_object* v_sproof_2366_){
_start:
{
if (lean_obj_tag(v_fproof_2364_) == 0)
{
lean_dec_ref(v_snd_2365_);
lean_dec(v___x_2362_);
if (lean_obj_tag(v_sproof_2366_) == 0)
{
lean_object* v___x_2367_; 
lean_dec_ref(v_fst_2363_);
lean_dec(v___x_2361_);
v___x_2367_ = lean_box(0);
return v___x_2367_;
}
else
{
lean_object* v_val_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2377_; 
v_val_2368_ = lean_ctor_get(v_sproof_2366_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_sproof_2366_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2370_ = v_sproof_2366_;
v_isShared_2371_ = v_isSharedCheck_2377_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_val_2368_);
lean_dec(v_sproof_2366_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2377_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2372_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_2361_, v_fst_2363_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v_val_2368_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2373_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_dec_ref(v_fst_2363_);
lean_dec(v___x_2361_);
if (lean_obj_tag(v_sproof_2366_) == 0)
{
lean_object* v_val_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2387_; 
v_val_2378_ = lean_ctor_get(v_fproof_2364_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_fproof_2364_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2380_ = v_fproof_2364_;
v_isShared_2381_ = v_isSharedCheck_2387_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_val_2378_);
lean_dec(v_fproof_2364_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2387_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2382_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_2362_, v_snd_2365_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v_val_2378_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2383_);
v___x_2385_ = v___x_2380_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
else
{
lean_object* v_val_2388_; lean_object* v_val_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_snd_2365_);
lean_dec(v___x_2362_);
v_val_2388_ = lean_ctor_get(v_fproof_2364_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v_fproof_2364_, 1);
v_val_2389_ = lean_ctor_get(v_sproof_2366_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_sproof_2366_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2391_ = v_sproof_2366_;
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_val_2389_);
lean_dec(v_sproof_2366_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_val_2388_);
lean_ctor_set(v___x_2393_, 1, v_val_2389_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2393_);
v___x_2395_ = v___x_2391_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(lean_object* v_width_2399_, lean_object* v_expr_2400_, lean_object* v_width_2401_, lean_object* v_expr_2402_, lean_object* v_val_2403_, lean_object* v_val_2404_, lean_object* v___x_2405_, lean_object* v___x_2406_, lean_object* v___x_2407_, lean_object* v___x_2408_, lean_object* v___x_2409_, lean_object* v___x_2410_, lean_object* v___x_2411_, lean_object* v_arg_2412_, lean_object* v_arg_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
lean_inc(v_width_2399_);
v___x_2426_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_2399_, v_expr_2400_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2428_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
lean_inc(v_width_2401_);
v___x_2428_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_2401_, v_expr_2402_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2430_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2430_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_2403_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2432_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_2404_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2460_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2460_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2460_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; 
lean_inc(v_a_2429_);
lean_inc(v_a_2427_);
v___x_2437_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__14(v_width_2399_, v_width_2401_, v_a_2427_, v_a_2431_, v_a_2429_, v_a_2433_);
if (lean_obj_tag(v___x_2437_) == 1)
{
lean_object* v_val_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2455_; 
v_val_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2455_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_val_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2455_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_fst_2442_; lean_object* v_snd_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
v_fst_2442_ = lean_ctor_get(v_val_2438_, 0);
lean_inc(v_fst_2442_);
v_snd_2443_ = lean_ctor_get(v_val_2438_, 1);
lean_inc(v_snd_2443_);
lean_dec(v_val_2438_);
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0));
v___x_2445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0));
v___x_2446_ = l_Lean_Name_mkStr6(v___x_2405_, v___x_2406_, v___x_2407_, v___x_2444_, v___x_2408_, v___x_2445_);
v___x_2447_ = l_Lean_mkConst(v___x_2446_, v___x_2409_);
v___x_2448_ = l_Lean_mkApp8(v___x_2447_, v___x_2410_, v___x_2411_, v_arg_2412_, v_a_2427_, v_arg_2413_, v_a_2429_, v_fst_2442_, v_snd_2443_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2448_);
v___x_2450_ = v___x_2440_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2450_);
v___x_2452_ = v___x_2435_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
lean_dec(v___x_2437_);
lean_dec(v_a_2429_);
lean_dec(v_a_2427_);
lean_dec_ref(v_arg_2413_);
lean_dec_ref(v_arg_2412_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec_ref(v___x_2408_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2405_);
v___x_2456_ = lean_box(0);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2456_);
v___x_2458_ = v___x_2435_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_dec(v_a_2431_);
lean_dec(v_a_2429_);
lean_dec(v_a_2427_);
lean_dec_ref(v_arg_2413_);
lean_dec_ref(v_arg_2412_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec_ref(v___x_2408_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2405_);
lean_dec(v_width_2401_);
lean_dec(v_width_2399_);
return v___x_2432_;
}
}
else
{
lean_dec(v_a_2429_);
lean_dec(v_a_2427_);
lean_dec_ref(v_arg_2413_);
lean_dec_ref(v_arg_2412_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec_ref(v___x_2408_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2405_);
lean_dec_ref(v_val_2404_);
lean_dec(v_width_2401_);
lean_dec(v_width_2399_);
return v___x_2430_;
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2427_);
lean_dec_ref(v_arg_2413_);
lean_dec_ref(v_arg_2412_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec_ref(v___x_2408_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2405_);
lean_dec_ref(v_val_2404_);
lean_dec_ref(v_val_2403_);
lean_dec(v_width_2401_);
lean_dec(v_width_2399_);
v_a_2461_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2428_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2428_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_arg_2413_);
lean_dec_ref(v_arg_2412_);
lean_dec_ref(v___x_2411_);
lean_dec_ref(v___x_2410_);
lean_dec(v___x_2409_);
lean_dec_ref(v___x_2408_);
lean_dec_ref(v___x_2407_);
lean_dec_ref(v___x_2406_);
lean_dec_ref(v___x_2405_);
lean_dec_ref(v_val_2404_);
lean_dec_ref(v_val_2403_);
lean_dec_ref(v_expr_2402_);
lean_dec(v_width_2401_);
lean_dec(v_width_2399_);
v_a_2469_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2426_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2426_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed(lean_object** _args){
lean_object* v_width_2477_ = _args[0];
lean_object* v_expr_2478_ = _args[1];
lean_object* v_width_2479_ = _args[2];
lean_object* v_expr_2480_ = _args[3];
lean_object* v_val_2481_ = _args[4];
lean_object* v_val_2482_ = _args[5];
lean_object* v___x_2483_ = _args[6];
lean_object* v___x_2484_ = _args[7];
lean_object* v___x_2485_ = _args[8];
lean_object* v___x_2486_ = _args[9];
lean_object* v___x_2487_ = _args[10];
lean_object* v___x_2488_ = _args[11];
lean_object* v___x_2489_ = _args[12];
lean_object* v_arg_2490_ = _args[13];
lean_object* v_arg_2491_ = _args[14];
lean_object* v___y_2492_ = _args[15];
lean_object* v___y_2493_ = _args[16];
lean_object* v___y_2494_ = _args[17];
lean_object* v___y_2495_ = _args[18];
lean_object* v___y_2496_ = _args[19];
lean_object* v___y_2497_ = _args[20];
lean_object* v___y_2498_ = _args[21];
lean_object* v___y_2499_ = _args[22];
lean_object* v___y_2500_ = _args[23];
lean_object* v___y_2501_ = _args[24];
lean_object* v___y_2502_ = _args[25];
lean_object* v___y_2503_ = _args[26];
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(v_width_2477_, v_expr_2478_, v_width_2479_, v_expr_2480_, v_val_2481_, v_val_2482_, v___x_2483_, v___x_2484_, v___x_2485_, v___x_2486_, v___x_2487_, v___x_2488_, v___x_2489_, v_arg_2490_, v_arg_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(lean_object* v_n_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_n_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2(lean_object* v_n_2507_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_n_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___redArg(lean_object* v_a_2509_, lean_object* v_x_2510_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_box(0);
return v___x_2511_;
}
else
{
lean_object* v_key_2512_; lean_object* v_value_2513_; lean_object* v_tail_2514_; size_t v___x_2515_; size_t v___x_2516_; uint8_t v___x_2517_; 
v_key_2512_ = lean_ctor_get(v_x_2510_, 0);
v_value_2513_ = lean_ctor_get(v_x_2510_, 1);
v_tail_2514_ = lean_ctor_get(v_x_2510_, 2);
v___x_2515_ = lean_ptr_addr(v_key_2512_);
v___x_2516_ = lean_ptr_addr(v_a_2509_);
v___x_2517_ = lean_usize_dec_eq(v___x_2515_, v___x_2516_);
if (v___x_2517_ == 0)
{
v_x_2510_ = v_tail_2514_;
goto _start;
}
else
{
lean_object* v___x_2519_; 
lean_inc(v_value_2513_);
v___x_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2519_, 0, v_value_2513_);
return v___x_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___redArg___boxed(lean_object* v_a_2520_, lean_object* v_x_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___redArg(v_a_2520_, v_x_2521_);
lean_dec(v_x_2521_);
lean_dec_ref(v_a_2520_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg(lean_object* v_m_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_buckets_2525_; lean_object* v___x_2526_; size_t v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; uint64_t v___x_2530_; uint64_t v___x_2531_; uint64_t v___x_2532_; uint64_t v_fold_2533_; uint64_t v___x_2534_; uint64_t v___x_2535_; uint64_t v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; size_t v___x_2539_; size_t v___x_2540_; size_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v_buckets_2525_ = lean_ctor_get(v_m_2523_, 1);
v___x_2526_ = lean_array_get_size(v_buckets_2525_);
v___x_2527_ = lean_ptr_addr(v_a_2524_);
v___x_2528_ = ((size_t)3ULL);
v___x_2529_ = lean_usize_shift_right(v___x_2527_, v___x_2528_);
v___x_2530_ = lean_usize_to_uint64(v___x_2529_);
v___x_2531_ = 32ULL;
v___x_2532_ = lean_uint64_shift_right(v___x_2530_, v___x_2531_);
v_fold_2533_ = lean_uint64_xor(v___x_2530_, v___x_2532_);
v___x_2534_ = 16ULL;
v___x_2535_ = lean_uint64_shift_right(v_fold_2533_, v___x_2534_);
v___x_2536_ = lean_uint64_xor(v_fold_2533_, v___x_2535_);
v___x_2537_ = lean_uint64_to_usize(v___x_2536_);
v___x_2538_ = lean_usize_of_nat(v___x_2526_);
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_sub(v___x_2538_, v___x_2539_);
v___x_2541_ = lean_usize_land(v___x_2537_, v___x_2540_);
v___x_2542_ = lean_array_uget_borrowed(v_buckets_2525_, v___x_2541_);
v___x_2543_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___redArg(v_a_2524_, v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg___boxed(lean_object* v_m_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg(v_m_2544_, v_a_2545_);
lean_dec_ref(v_a_2545_);
lean_dec_ref(v_m_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___lam__0(lean_object* v___x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2547_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___lam__0___boxed(lean_object* v___x_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___lam__0(v___x_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(lean_object* v_width_2576_, lean_object* v_expr_2577_, lean_object* v_a_2578_, lean_object* v___x_2579_, lean_object* v___x_2580_, lean_object* v___x_2581_, lean_object* v___x_2582_, lean_object* v_e_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; 
lean_inc(v_width_2576_);
v___x_2596_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_2576_, v_expr_2577_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_a_2578_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2617_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2617_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2617_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___y_2604_; 
if (lean_obj_tag(v_a_2599_) == 0)
{
lean_object* v___x_2615_; 
lean_inc(v_a_2597_);
v___x_2615_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v_width_2576_, v_a_2597_);
v___y_2604_ = v___x_2615_;
goto v___jp_2603_;
}
else
{
lean_object* v_val_2616_; 
lean_dec(v_width_2576_);
v_val_2616_ = lean_ctor_get(v_a_2599_, 0);
lean_inc(v_val_2616_);
lean_dec_ref_known(v_a_2599_, 1);
v___y_2604_ = v_val_2616_;
goto v___jp_2603_;
}
v___jp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0));
v___x_2606_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0));
v___x_2607_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0));
v___x_2608_ = l_Lean_Name_mkStr6(v___x_2579_, v___x_2580_, v___x_2581_, v___x_2605_, v___x_2606_, v___x_2607_);
v___x_2609_ = l_Lean_mkConst(v___x_2608_, v___x_2582_);
v___x_2610_ = l_Lean_mkApp3(v___x_2609_, v_e_2583_, v_a_2597_, v___y_2604_);
v___x_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2611_);
v___x_2613_ = v___x_2601_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_dec(v_a_2597_);
lean_dec_ref(v_e_2583_);
lean_dec(v___x_2582_);
lean_dec_ref(v___x_2581_);
lean_dec_ref(v___x_2580_);
lean_dec_ref(v___x_2579_);
lean_dec(v_width_2576_);
return v___x_2598_;
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v_e_2583_);
lean_dec(v___x_2582_);
lean_dec_ref(v___x_2581_);
lean_dec_ref(v___x_2580_);
lean_dec_ref(v___x_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_width_2576_);
v_a_2618_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2596_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2596_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed(lean_object** _args){
lean_object* v_width_2626_ = _args[0];
lean_object* v_expr_2627_ = _args[1];
lean_object* v_a_2628_ = _args[2];
lean_object* v___x_2629_ = _args[3];
lean_object* v___x_2630_ = _args[4];
lean_object* v___x_2631_ = _args[5];
lean_object* v___x_2632_ = _args[6];
lean_object* v_e_2633_ = _args[7];
lean_object* v___y_2634_ = _args[8];
lean_object* v___y_2635_ = _args[9];
lean_object* v___y_2636_ = _args[10];
lean_object* v___y_2637_ = _args[11];
lean_object* v___y_2638_ = _args[12];
lean_object* v___y_2639_ = _args[13];
lean_object* v___y_2640_ = _args[14];
lean_object* v___y_2641_ = _args[15];
lean_object* v___y_2642_ = _args[16];
lean_object* v___y_2643_ = _args[17];
lean_object* v___y_2644_ = _args[18];
lean_object* v___y_2645_ = _args[19];
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(v_width_2626_, v_expr_2627_, v_a_2628_, v___x_2629_, v___x_2630_, v___x_2631_, v___x_2632_, v_e_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(lean_object* v_distanceExpr_2720_, lean_object* v_innerExpr_2721_, lean_object* v_shiftOp_2722_, lean_object* v_shiftOpName_2723_, lean_object* v_congrThm_2724_, lean_object* v_origExpr_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___x_2739_; 
lean_inc_ref(v_innerExpr_2721_);
v___x_2739_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_2721_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2800_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2800_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2800_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
if (lean_obj_tag(v_a_2740_) == 1)
{
lean_object* v_val_2744_; lean_object* v___x_2745_; 
lean_del_object(v___x_2742_);
v_val_2744_ = lean_ctor_get(v_a_2740_, 0);
lean_inc(v_val_2744_);
lean_dec_ref_known(v_a_2740_, 1);
lean_inc_ref(v_distanceExpr_2720_);
v___x_2745_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_distanceExpr_2720_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2795_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2795_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2795_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
if (lean_obj_tag(v_a_2746_) == 1)
{
lean_object* v_val_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2790_; 
lean_del_object(v___x_2748_);
v_val_2750_ = lean_ctor_get(v_a_2746_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_a_2746_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2752_ = v_a_2746_;
v_isShared_2753_ = v_isSharedCheck_2790_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_val_2750_);
lean_dec(v_a_2746_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2790_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_width_2754_; lean_object* v_bvExpr_2755_; lean_object* v_expr_2756_; lean_object* v_width_2757_; lean_object* v_bvExpr_2758_; lean_object* v_expr_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v_width_2754_ = lean_ctor_get(v_val_2744_, 0);
lean_inc_n(v_width_2754_, 3);
v_bvExpr_2755_ = lean_ctor_get(v_val_2744_, 1);
v_expr_2756_ = lean_ctor_get(v_val_2744_, 4);
v_width_2757_ = lean_ctor_get(v_val_2750_, 0);
v_bvExpr_2758_ = lean_ctor_get(v_val_2750_, 1);
v_expr_2759_ = lean_ctor_get(v_val_2750_, 4);
lean_inc_ref(v_bvExpr_2758_);
lean_inc_ref(v_bvExpr_2755_);
lean_inc_n(v_width_2757_, 2);
v___x_2760_ = lean_apply_4(v_shiftOp_2722_, v_width_2754_, v_width_2757_, v_bvExpr_2755_, v_bvExpr_2758_);
v___x_2761_ = lean_box(0);
v___x_2762_ = l_Lean_mkConst(v_shiftOpName_2723_, v___x_2761_);
v___x_2763_ = l_Lean_mkNatLit(v_width_2754_);
v___x_2764_ = l_Lean_mkNatLit(v_width_2757_);
lean_inc_ref(v_expr_2759_);
lean_inc_ref(v_expr_2756_);
lean_inc_ref(v___x_2764_);
lean_inc_ref(v___x_2763_);
v___x_2765_ = l_Lean_mkApp4(v___x_2762_, v___x_2763_, v___x_2764_, v_expr_2756_, v_expr_2759_);
v___x_2766_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2765_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2781_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2771_ = l_Lean_mkConst(v_congrThm_2724_, v___x_2761_);
v___x_2772_ = l_Lean_mkAppB(v___x_2771_, v___x_2763_, v___x_2764_);
v___x_2773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed), 17, 5);
lean_closure_set(v___x_2773_, 0, v_val_2744_);
lean_closure_set(v___x_2773_, 1, v_val_2750_);
lean_closure_set(v___x_2773_, 2, v_innerExpr_2721_);
lean_closure_set(v___x_2773_, 3, v_distanceExpr_2720_);
lean_closure_set(v___x_2773_, 4, v___x_2772_);
v___x_2774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2774_, 0, v_width_2754_);
lean_ctor_set(v___x_2774_, 1, v___x_2760_);
lean_ctor_set(v___x_2774_, 2, v_origExpr_2725_);
lean_ctor_set(v___x_2774_, 3, v___x_2773_);
lean_ctor_set(v___x_2774_, 4, v_a_2767_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 0, v___x_2774_);
v___x_2776_ = v___x_2752_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2776_);
v___x_2778_ = v___x_2769_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref(v___x_2764_);
lean_dec_ref(v___x_2763_);
lean_dec_ref(v___x_2760_);
lean_dec(v_width_2754_);
lean_del_object(v___x_2752_);
lean_dec(v_val_2750_);
lean_dec(v_val_2744_);
lean_dec_ref(v_origExpr_2725_);
lean_dec(v_congrThm_2724_);
lean_dec_ref(v_innerExpr_2721_);
lean_dec_ref(v_distanceExpr_2720_);
v_a_2782_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2766_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2766_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2793_; 
lean_dec(v_a_2746_);
lean_dec(v_val_2744_);
lean_dec_ref(v_origExpr_2725_);
lean_dec(v_congrThm_2724_);
lean_dec(v_shiftOpName_2723_);
lean_dec_ref(v_shiftOp_2722_);
lean_dec_ref(v_innerExpr_2721_);
lean_dec_ref(v_distanceExpr_2720_);
v___x_2791_ = lean_box(0);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2791_);
v___x_2793_ = v___x_2748_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_dec(v_val_2744_);
lean_dec_ref(v_origExpr_2725_);
lean_dec(v_congrThm_2724_);
lean_dec(v_shiftOpName_2723_);
lean_dec_ref(v_shiftOp_2722_);
lean_dec_ref(v_innerExpr_2721_);
lean_dec_ref(v_distanceExpr_2720_);
return v___x_2745_;
}
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
lean_dec(v_a_2740_);
lean_dec_ref(v_origExpr_2725_);
lean_dec(v_congrThm_2724_);
lean_dec(v_shiftOpName_2723_);
lean_dec_ref(v_shiftOp_2722_);
lean_dec_ref(v_innerExpr_2721_);
lean_dec_ref(v_distanceExpr_2720_);
v___x_2796_ = lean_box(0);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2796_);
v___x_2798_ = v___x_2742_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_2725_);
lean_dec(v_congrThm_2724_);
lean_dec(v_shiftOpName_2723_);
lean_dec_ref(v_shiftOp_2722_);
lean_dec_ref(v_innerExpr_2721_);
lean_dec_ref(v_distanceExpr_2720_);
return v___x_2739_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = lean_box(0);
v___x_2877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1));
v___x_2878_ = l_Lean_mkConst(v___x_2877_, v___x_2876_);
return v___x_2878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2887_ = lean_box(0);
v___x_2888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5));
v___x_2889_ = l_Lean_mkConst(v___x_2888_, v___x_2887_);
return v___x_2889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_box(0);
v___x_2898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8));
v___x_2899_ = l_Lean_mkConst(v___x_2898_, v___x_2897_);
return v___x_2899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_box(0);
v___x_2908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11));
v___x_2909_ = l_Lean_mkConst(v___x_2908_, v___x_2907_);
return v___x_2909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_box(0);
v___x_2918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14));
v___x_2919_ = l_Lean_mkConst(v___x_2918_, v___x_2917_);
return v___x_2919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_box(0);
v___x_2928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17));
v___x_2929_ = l_Lean_mkConst(v___x_2928_, v___x_2927_);
return v___x_2929_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20));
v___x_2939_ = l_Lean_mkConst(v___x_2938_, v___x_2937_);
return v___x_2939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_box(0);
v___x_2948_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23));
v___x_2949_ = l_Lean_mkConst(v___x_2948_, v___x_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(lean_object* v_lhsExpr_2950_, lean_object* v_rhsExpr_2951_, uint8_t v_op_2952_, lean_object* v_congrThm_2953_, lean_object* v_origExpr_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v___x_2968_; 
lean_inc_ref(v_lhsExpr_2950_);
v___x_2968_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_lhsExpr_2950_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_3042_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_3042_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_3042_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
if (lean_obj_tag(v_a_2969_) == 1)
{
lean_object* v_val_2973_; lean_object* v___x_2974_; 
lean_del_object(v___x_2971_);
v_val_2973_ = lean_ctor_get(v_a_2969_, 0);
lean_inc(v_val_2973_);
lean_dec_ref_known(v_a_2969_, 1);
lean_inc_ref(v_rhsExpr_2951_);
v___x_2974_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_rhsExpr_2951_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3037_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_2977_ = v___x_2974_;
v_isShared_2978_ = v_isSharedCheck_3037_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3037_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
if (lean_obj_tag(v_a_2975_) == 1)
{
lean_object* v_val_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3032_; 
v_val_2979_ = lean_ctor_get(v_a_2975_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_a_2975_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_2981_ = v_a_2975_;
v_isShared_2982_ = v_isSharedCheck_3032_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_val_2979_);
lean_dec(v_a_2975_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3032_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v_width_2983_; lean_object* v_bvExpr_2984_; lean_object* v_expr_2985_; lean_object* v_width_2986_; lean_object* v_bvExpr_2987_; lean_object* v_expr_2988_; uint8_t v___x_2989_; 
v_width_2983_ = lean_ctor_get(v_val_2979_, 0);
v_bvExpr_2984_ = lean_ctor_get(v_val_2979_, 1);
v_expr_2985_ = lean_ctor_get(v_val_2979_, 4);
v_width_2986_ = lean_ctor_get(v_val_2973_, 0);
lean_inc(v_width_2986_);
v_bvExpr_2987_ = lean_ctor_get(v_val_2973_, 1);
v_expr_2988_ = lean_ctor_get(v_val_2973_, 4);
v___x_2989_ = lean_nat_dec_eq(v_width_2983_, v_width_2986_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_dec(v_width_2986_);
lean_del_object(v___x_2981_);
lean_dec(v_val_2979_);
lean_dec(v_val_2973_);
lean_dec_ref(v_origExpr_2954_);
lean_dec(v_congrThm_2953_);
lean_dec_ref(v_rhsExpr_2951_);
lean_dec_ref(v_lhsExpr_2950_);
v___x_2990_ = lean_box(0);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2990_);
v___x_2992_ = v___x_2977_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___y_2999_; 
lean_del_object(v___x_2977_);
lean_inc_ref(v_bvExpr_2984_);
lean_inc_ref(v_bvExpr_2987_);
lean_inc_n(v_width_2986_, 2);
v___x_2994_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_width_2986_, v_bvExpr_2987_, v_op_2952_, v_bvExpr_2984_);
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2);
v___x_2997_ = l_Lean_mkNatLit(v_width_2986_);
switch(v_op_2952_)
{
case 0:
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6);
v___y_2999_ = v___x_3025_;
goto v___jp_2998_;
}
case 1:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9);
v___y_2999_ = v___x_3026_;
goto v___jp_2998_;
}
case 2:
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12);
v___y_2999_ = v___x_3027_;
goto v___jp_2998_;
}
case 3:
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15);
v___y_2999_ = v___x_3028_;
goto v___jp_2998_;
}
case 4:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18);
v___y_2999_ = v___x_3029_;
goto v___jp_2998_;
}
case 5:
{
lean_object* v___x_3030_; 
v___x_3030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21);
v___y_2999_ = v___x_3030_;
goto v___jp_2998_;
}
default: 
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24);
v___y_2999_ = v___x_3031_;
goto v___jp_2998_;
}
}
v___jp_2998_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_inc_ref(v_expr_2985_);
lean_inc_ref(v___y_2999_);
lean_inc_ref(v_expr_2988_);
lean_inc_ref(v___x_2997_);
v___x_3000_ = l_Lean_mkApp4(v___x_2996_, v___x_2997_, v_expr_2988_, v___y_2999_, v_expr_2985_);
v___x_3001_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3000_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3016_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3016_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3016_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3006_ = l_Lean_mkConst(v_congrThm_2953_, v___x_2995_);
v___x_3007_ = l_Lean_Expr_app___override(v___x_3006_, v___x_2997_);
v___x_3008_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed), 17, 5);
lean_closure_set(v___x_3008_, 0, v_val_2973_);
lean_closure_set(v___x_3008_, 1, v_val_2979_);
lean_closure_set(v___x_3008_, 2, v_lhsExpr_2950_);
lean_closure_set(v___x_3008_, 3, v_rhsExpr_2951_);
lean_closure_set(v___x_3008_, 4, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3009_, 0, v_width_2986_);
lean_ctor_set(v___x_3009_, 1, v___x_2994_);
lean_ctor_set(v___x_3009_, 2, v_origExpr_2954_);
lean_ctor_set(v___x_3009_, 3, v___x_3008_);
lean_ctor_set(v___x_3009_, 4, v_a_3002_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_3009_);
v___x_3011_ = v___x_2981_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3013_; 
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3011_);
v___x_3013_ = v___x_3004_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v___x_2997_);
lean_dec_ref(v___x_2994_);
lean_dec(v_width_2986_);
lean_del_object(v___x_2981_);
lean_dec(v_val_2979_);
lean_dec(v_val_2973_);
lean_dec_ref(v_origExpr_2954_);
lean_dec(v_congrThm_2953_);
lean_dec_ref(v_rhsExpr_2951_);
lean_dec_ref(v_lhsExpr_2950_);
v_a_3017_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3001_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3001_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_dec(v_a_2975_);
lean_dec(v_val_2973_);
lean_dec_ref(v_origExpr_2954_);
lean_dec(v_congrThm_2953_);
lean_dec_ref(v_rhsExpr_2951_);
lean_dec_ref(v_lhsExpr_2950_);
v___x_3033_ = lean_box(0);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_3033_);
v___x_3035_ = v___x_2977_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_dec(v_val_2973_);
lean_dec_ref(v_origExpr_2954_);
lean_dec(v_congrThm_2953_);
lean_dec_ref(v_rhsExpr_2951_);
lean_dec_ref(v_lhsExpr_2950_);
return v___x_2974_;
}
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_dec(v_a_2969_);
lean_dec_ref(v_origExpr_2954_);
lean_dec(v_congrThm_2953_);
lean_dec_ref(v_rhsExpr_2951_);
lean_dec_ref(v_lhsExpr_2950_);
v___x_3038_ = lean_box(0);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_3038_);
v___x_3040_ = v___x_2971_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_2954_);
lean_dec(v_congrThm_2953_);
lean_dec_ref(v_rhsExpr_2951_);
lean_dec_ref(v_lhsExpr_2950_);
return v___x_2968_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71));
v___x_3085_ = l_Lean_stringToMessageData(v___x_3084_);
return v___x_3085_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_box(0);
v___x_3094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74));
v___x_3095_ = l_Lean_mkConst(v___x_3094_, v___x_3093_);
return v___x_3095_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81));
v___x_3120_ = l_Lean_mkConst(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__2(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_box(0);
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__1));
v___x_3130_ = l_Lean_mkConst(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(lean_object* v_lhsExpr_3152_, lean_object* v_rhsExpr_3153_, uint8_t v_pred_3154_, lean_object* v_origExpr_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v___x_3169_; 
lean_inc_ref(v_lhsExpr_3152_);
v___x_3169_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_lhsExpr_3152_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3199_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3199_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3199_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
if (lean_obj_tag(v_a_3170_) == 1)
{
lean_object* v_val_3174_; lean_object* v___x_3175_; 
lean_del_object(v___x_3172_);
v_val_3174_ = lean_ctor_get(v_a_3170_, 0);
lean_inc(v_val_3174_);
lean_dec_ref_known(v_a_3170_, 1);
lean_inc_ref(v_rhsExpr_3153_);
v___x_3175_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_rhsExpr_3153_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3186_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3186_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3186_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
if (lean_obj_tag(v_a_3176_) == 1)
{
lean_object* v_val_3180_; lean_object* v___x_3181_; 
lean_del_object(v___x_3178_);
v_val_3180_ = lean_ctor_get(v_a_3176_, 0);
lean_inc(v_val_3180_);
lean_dec_ref_known(v_a_3176_, 1);
v___x_3181_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_val_3174_, v_val_3180_, v_lhsExpr_3152_, v_rhsExpr_3153_, v_pred_3154_, v_origExpr_3155_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
lean_dec(v_a_3176_);
lean_dec(v_val_3174_);
lean_dec_ref(v_origExpr_3155_);
lean_dec_ref(v_rhsExpr_3153_);
lean_dec_ref(v_lhsExpr_3152_);
v___x_3182_ = lean_box(0);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3182_);
v___x_3184_ = v___x_3178_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_val_3174_);
lean_dec_ref(v_origExpr_3155_);
lean_dec_ref(v_rhsExpr_3153_);
lean_dec_ref(v_lhsExpr_3152_);
v_a_3187_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3175_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3175_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_dec(v_a_3170_);
lean_dec_ref(v_origExpr_3155_);
lean_dec_ref(v_rhsExpr_3153_);
lean_dec_ref(v_lhsExpr_3152_);
v___x_3195_ = lean_box(0);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3195_);
v___x_3197_ = v___x_3172_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v_origExpr_3155_);
lean_dec_ref(v_rhsExpr_3153_);
lean_dec_ref(v_lhsExpr_3152_);
v_a_3200_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3169_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3169_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(lean_object* v_origExpr_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v___x_3228_; 
lean_inc_ref(v_origExpr_3208_);
v___x_3228_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_3208_, v_a_3218_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v___x_3230_ = l_Lean_Expr_cleanupAnnotations(v_a_3229_);
v___x_3231_ = l_Lean_Expr_isApp(v___x_3230_);
if (v___x_3231_ == 0)
{
lean_dec_ref(v___x_3230_);
lean_dec_ref(v_origExpr_3208_);
goto v___jp_3222_;
}
else
{
lean_object* v_arg_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_arg_3232_ = lean_ctor_get(v___x_3230_, 1);
lean_inc_ref(v_arg_3232_);
v___x_3233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3230_);
v___x_3234_ = l_Lean_Expr_isApp(v___x_3233_);
if (v___x_3234_ == 0)
{
lean_dec_ref(v___x_3233_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
goto v___jp_3222_;
}
else
{
lean_object* v_arg_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v_arg_3235_ = lean_ctor_get(v___x_3233_, 1);
lean_inc_ref(v_arg_3235_);
v___x_3236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3233_);
v___x_3237_ = l_Lean_Expr_isApp(v___x_3236_);
if (v___x_3237_ == 0)
{
lean_dec_ref(v___x_3236_);
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
goto v___jp_3222_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
v___x_3238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3236_);
v___x_3239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0));
v___x_3240_ = l_Lean_Expr_isConstOf(v___x_3238_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2));
v___x_3242_ = l_Lean_Expr_isConstOf(v___x_3238_, v___x_3241_);
if (v___x_3242_ == 0)
{
uint8_t v___x_3243_; 
v___x_3243_ = l_Lean_Expr_isApp(v___x_3238_);
if (v___x_3243_ == 0)
{
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
goto v___jp_3222_;
}
else
{
lean_object* v_arg_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v_arg_3244_ = lean_ctor_get(v___x_3238_, 1);
lean_inc_ref(v_arg_3244_);
v___x_3245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3238_);
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5));
v___x_3247_ = l_Lean_Expr_isConstOf(v___x_3245_, v___x_3246_);
lean_dec_ref(v___x_3245_);
if (v___x_3247_ == 0)
{
lean_dec_ref(v_arg_3244_);
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
goto v___jp_3222_;
}
else
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = l_Lean_Expr_cleanupAnnotations(v_arg_3244_);
v___x_3249_ = l_Lean_Expr_isApp(v___x_3248_);
if (v___x_3249_ == 0)
{
lean_dec_ref(v___x_3248_);
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
goto v___jp_3225_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3248_);
v___x_3251_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1));
v___x_3252_ = l_Lean_Expr_isConstOf(v___x_3250_, v___x_3251_);
lean_dec_ref(v___x_3250_);
if (v___x_3252_ == 0)
{
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
goto v___jp_3225_;
}
else
{
uint8_t v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = 0;
v___x_3254_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_arg_3235_, v_arg_3232_, v___x_3253_, v_origExpr_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
return v___x_3254_;
}
}
}
}
}
else
{
uint8_t v___x_3255_; lean_object* v___x_3256_; 
lean_dec_ref(v___x_3238_);
v___x_3255_ = 1;
v___x_3256_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_arg_3235_, v_arg_3232_, v___x_3255_, v_origExpr_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
return v___x_3256_;
}
}
else
{
lean_object* v___x_3257_; 
lean_dec_ref(v___x_3238_);
lean_inc_ref(v_arg_3235_);
v___x_3257_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_arg_3235_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3297_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3297_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3297_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
if (lean_obj_tag(v_a_3258_) == 1)
{
lean_object* v_val_3262_; lean_object* v___x_3263_; 
v_val_3262_ = lean_ctor_get(v_a_3258_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v_a_3258_, 1);
v___x_3263_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_3232_);
if (lean_obj_tag(v___x_3263_) == 1)
{
lean_object* v_val_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3288_; 
lean_del_object(v___x_3260_);
v_val_3264_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3266_ = v___x_3263_;
v_isShared_3267_ = v_isSharedCheck_3288_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_val_3264_);
lean_dec(v___x_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3288_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(v_val_3262_, v_arg_3235_, v_val_3264_, v_origExpr_3208_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3279_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3279_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3279_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v_a_3269_);
v___x_3274_ = v___x_3266_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3276_; 
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 0, v___x_3274_);
v___x_3276_ = v___x_3271_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_del_object(v___x_3266_);
v_a_3280_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3268_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3268_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
else
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
lean_dec(v___x_3263_);
lean_dec(v_val_3262_);
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_origExpr_3208_);
v___x_3289_ = lean_box(0);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3289_);
v___x_3291_ = v___x_3260_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
lean_dec(v_a_3258_);
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
v___x_3293_ = lean_box(0);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3293_);
v___x_3295_ = v___x_3260_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v_arg_3235_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_origExpr_3208_);
v_a_3298_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3257_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3257_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
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
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v_origExpr_3208_);
v_a_3306_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3228_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3228_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
v___jp_3222_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
return v___x_3224_;
}
v___jp_3225_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(0);
v___x_3322_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2));
v___x_3323_ = l_Lean_mkConst(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = l_Lean_mkNatLit(v___x_3324_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = lean_unsigned_to_nat(0u);
v___x_3327_ = l_Lean_mkNatLit(v___x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(lean_object* v_e_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v___x_3342_; 
lean_inc_ref(v_e_3328_);
v___x_3342_ = l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg(v_e_3328_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3407_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3407_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3407_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
uint8_t v___x_3347_; 
v___x_3347_ = lean_unbox(v_a_3343_);
lean_dec(v_a_3343_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
lean_dec_ref(v_e_3328_);
v___x_3348_ = lean_box(0);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3348_);
v___x_3350_ = v___x_3345_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
else
{
lean_object* v___x_3352_; 
lean_del_object(v___x_3345_);
lean_inc_ref(v_e_3328_);
v___x_3352_ = l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(v_e_3328_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3352_, 1);
v___x_3354_ = lean_unsigned_to_nat(1u);
v___x_3355_ = 0;
v___x_3356_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom(v_a_3353_, v___x_3354_, v___x_3355_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v_width_3358_; lean_object* v_bvExpr_3359_; lean_object* v_expr_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___f_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v_width_3358_ = lean_ctor_get(v_a_3357_, 0);
lean_inc_n(v_width_3358_, 2);
v_bvExpr_3359_ = lean_ctor_get(v_a_3357_, 1);
v_expr_3360_ = lean_ctor_get(v_a_3357_, 4);
lean_inc_ref_n(v_expr_3360_, 2);
v___x_3361_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_bvExpr_3359_);
v___x_3362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3362_, 0, v_width_3358_);
lean_ctor_set(v___x_3362_, 1, v_bvExpr_3359_);
lean_ctor_set(v___x_3362_, 2, v___x_3361_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_3364_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1));
v___x_3365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_3366_ = lean_box(0);
lean_inc_ref(v_e_3328_);
v___f_3367_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed), 20, 8);
lean_closure_set(v___f_3367_, 0, v_width_3358_);
lean_closure_set(v___f_3367_, 1, v_expr_3360_);
lean_closure_set(v___f_3367_, 2, v_a_3357_);
lean_closure_set(v___f_3367_, 3, v___x_3363_);
lean_closure_set(v___f_3367_, 4, v___x_3364_);
lean_closure_set(v___f_3367_, 5, v___x_3365_);
lean_closure_set(v___f_3367_, 6, v___x_3366_);
lean_closure_set(v___f_3367_, 7, v_e_3328_);
v___x_3368_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3);
v___x_3369_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4);
v___x_3370_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5);
v___x_3371_ = l_Lean_mkApp3(v___x_3368_, v___x_3369_, v_expr_3360_, v___x_3370_);
v___x_3372_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3371_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3382_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3382_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3362_);
lean_ctor_set(v___x_3377_, 1, v_e_3328_);
lean_ctor_set(v___x_3377_, 2, v___f_3367_);
lean_ctor_set(v___x_3377_, 3, v_a_3373_);
v___x_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3378_);
v___x_3380_ = v___x_3375_;
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
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v___f_3367_);
lean_dec_ref_known(v___x_3362_, 3);
lean_dec_ref(v_e_3328_);
v_a_3383_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3372_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3372_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v_e_3328_);
v_a_3391_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3356_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3356_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v_e_3328_);
v_a_3399_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3352_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3352_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v_e_3328_);
v_a_3408_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3342_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3342_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__23(lean_object* v_e_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v___y_3431_; lean_object* v___x_3454_; lean_object* v_bvPredCache_3455_; lean_object* v___x_3456_; 
v___x_3454_ = lean_st_ref_get(v_a_3417_);
v_bvPredCache_3455_ = lean_ctor_get(v___x_3454_, 2);
lean_inc_ref(v_bvPredCache_3455_);
lean_dec(v___x_3454_);
v___x_3456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg(v_bvPredCache_3455_, v_e_3416_);
lean_dec_ref(v_bvPredCache_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v___x_3457_; 
lean_inc_ref(v_e_3416_);
v___x_3457_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_e_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
if (lean_obj_tag(v_a_3458_) == 0)
{
lean_object* v___x_3459_; 
lean_dec_ref_known(v___x_3457_, 1);
lean_inc_ref(v_e_3416_);
v___x_3459_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(v_e_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
v___y_3431_ = v___x_3459_;
goto v___jp_3430_;
}
else
{
v___y_3431_ = v___x_3457_;
goto v___jp_3430_;
}
}
else
{
v___y_3431_ = v___x_3457_;
goto v___jp_3430_;
}
}
else
{
lean_object* v_val_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v_e_3416_);
v_val_3460_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3456_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_val_3460_);
lean_dec(v___x_3456_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 0);
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_val_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
v___jp_3430_:
{
if (lean_obj_tag(v___y_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3453_; 
v_a_3432_ = lean_ctor_get(v___y_3431_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___y_3431_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3434_ = v___y_3431_;
v_isShared_3435_ = v_isSharedCheck_3453_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___y_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3453_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v_lemmas_3437_; lean_object* v_bvExprCache_3438_; lean_object* v_bvPredCache_3439_; lean_object* v_bvLogicalCache_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3452_; 
v___x_3436_ = lean_st_ref_take(v_a_3417_);
v_lemmas_3437_ = lean_ctor_get(v___x_3436_, 0);
v_bvExprCache_3438_ = lean_ctor_get(v___x_3436_, 1);
v_bvPredCache_3439_ = lean_ctor_get(v___x_3436_, 2);
v_bvLogicalCache_3440_ = lean_ctor_get(v___x_3436_, 3);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3442_ = v___x_3436_;
v_isShared_3443_ = v_isSharedCheck_3452_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_bvLogicalCache_3440_);
lean_inc(v_bvPredCache_3439_);
lean_inc(v_bvExprCache_3438_);
lean_inc(v_lemmas_3437_);
lean_dec(v___x_3436_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3452_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3446_; 
lean_inc(v_a_3432_);
v___x_3444_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17___redArg(v_bvPredCache_3439_, v_e_3416_, v_a_3432_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 2, v___x_3444_);
v___x_3446_ = v___x_3442_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_lemmas_3437_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_bvExprCache_3438_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_bvLogicalCache_3440_);
v___x_3446_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3447_ = lean_st_ref_put(v_a_3417_, v___x_3446_);
if (v_isShared_3435_ == 0)
{
v___x_3449_ = v___x_3434_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3432_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3416_);
return v___y_3431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(lean_object* v_origExpr_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__23(v_origExpr_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(lean_object* v_origExpr_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(v_origExpr_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3531_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3531_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3531_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
if (lean_obj_tag(v_a_3498_) == 1)
{
lean_object* v_val_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3526_; 
lean_del_object(v___x_3500_);
v_val_3502_ = lean_ctor_get(v_a_3498_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_a_3498_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3504_ = v_a_3498_;
v_isShared_3505_ = v_isSharedCheck_3526_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_val_3502_);
lean_dec(v_a_3498_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3526_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_3502_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3517_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3517_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3517_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v_a_3507_);
v___x_3512_ = v___x_3504_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3512_);
v___x_3514_ = v___x_3509_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_del_object(v___x_3504_);
v_a_3518_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3506_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3506_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
lean_dec(v_a_3498_);
v___x_3527_ = lean_box(0);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3527_);
v___x_3529_ = v___x_3500_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
v_a_3532_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3497_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3497_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(lean_object* v_lhsExpr_3550_, lean_object* v_rhsExpr_3551_, uint8_t v_gate_3552_, lean_object* v_origExpr_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v___x_3567_; 
lean_inc_ref(v_lhsExpr_3550_);
v___x_3567_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_lhsExpr_3550_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3612_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3612_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3612_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
if (lean_obj_tag(v_a_3568_) == 1)
{
lean_object* v_val_3572_; lean_object* v___x_3573_; 
lean_del_object(v___x_3570_);
v_val_3572_ = lean_ctor_get(v_a_3568_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v_a_3568_, 1);
lean_inc_ref(v_rhsExpr_3551_);
v___x_3573_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_rhsExpr_3551_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3607_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3607_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3607_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
if (lean_obj_tag(v_a_3574_) == 1)
{
lean_object* v_val_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3602_; 
lean_del_object(v___x_3576_);
v_val_3578_ = lean_ctor_get(v_a_3574_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_a_3574_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3580_ = v_a_3574_;
v_isShared_3581_ = v_isSharedCheck_3602_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_val_3578_);
lean_dec(v_a_3574_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3602_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_val_3572_, v_val_3578_, v_lhsExpr_3550_, v_rhsExpr_3551_, v_gate_3552_, v_origExpr_3553_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3593_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v_a_3583_);
v___x_3588_ = v___x_3580_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; 
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3588_);
v___x_3590_ = v___x_3585_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_del_object(v___x_3580_);
v_a_3594_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3582_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3582_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec(v_a_3574_);
lean_dec(v_val_3572_);
lean_dec_ref(v_origExpr_3553_);
lean_dec_ref(v_rhsExpr_3551_);
lean_dec_ref(v_lhsExpr_3550_);
v___x_3603_ = lean_box(0);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3603_);
v___x_3605_ = v___x_3576_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
else
{
lean_dec(v_val_3572_);
lean_dec_ref(v_origExpr_3553_);
lean_dec_ref(v_rhsExpr_3551_);
lean_dec_ref(v_lhsExpr_3550_);
return v___x_3573_;
}
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
lean_dec(v_a_3568_);
lean_dec_ref(v_origExpr_3553_);
lean_dec_ref(v_rhsExpr_3551_);
lean_dec_ref(v_lhsExpr_3550_);
v___x_3608_ = lean_box(0);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3608_);
v___x_3610_ = v___x_3570_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_3553_);
lean_dec_ref(v_rhsExpr_3551_);
lean_dec_ref(v_lhsExpr_3550_);
return v___x_3567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(lean_object* v_origExpr_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0));
v___x_3631_ = l_Lean_Core_checkSystem(v___x_3630_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v___x_3632_; 
lean_dec_ref_known(v___x_3631_, 1);
lean_inc_ref(v_origExpr_3613_);
v___x_3632_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_3613_, v_a_3623_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3634_ = l_Lean_Expr_cleanupAnnotations(v_a_3633_);
v___x_3635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1));
v___x_3636_ = l_Lean_Expr_isConstOf(v___x_3634_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2));
v___x_3638_ = l_Lean_Expr_isConstOf(v___x_3634_, v___x_3637_);
if (v___x_3638_ == 0)
{
uint8_t v___x_3639_; 
v___x_3639_ = l_Lean_Expr_isApp(v___x_3634_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
lean_dec_ref(v___x_3634_);
v___x_3640_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3640_;
}
else
{
lean_object* v_arg_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v_arg_3641_ = lean_ctor_get(v___x_3634_, 1);
lean_inc_ref(v_arg_3641_);
v___x_3642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3634_);
v___x_3643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3));
v___x_3644_ = l_Lean_Expr_isConstOf(v___x_3642_, v___x_3643_);
if (v___x_3644_ == 0)
{
uint8_t v___x_3645_; 
v___x_3645_ = l_Lean_Expr_isApp(v___x_3642_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; 
lean_dec_ref(v___x_3642_);
lean_dec_ref(v_arg_3641_);
v___x_3646_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3646_;
}
else
{
lean_object* v_arg_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v_arg_3647_ = lean_ctor_get(v___x_3642_, 1);
lean_inc_ref(v_arg_3647_);
v___x_3648_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3642_);
v___x_3649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4));
v___x_3650_ = l_Lean_Expr_isConstOf(v___x_3648_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5));
v___x_3652_ = l_Lean_Expr_isConstOf(v___x_3648_, v___x_3651_);
if (v___x_3652_ == 0)
{
uint8_t v___x_3653_; 
v___x_3653_ = l_Lean_Expr_isApp(v___x_3648_);
if (v___x_3653_ == 0)
{
lean_object* v___x_3654_; 
lean_dec_ref(v___x_3648_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
v___x_3654_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3654_;
}
else
{
lean_object* v_arg_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v_arg_3655_ = lean_ctor_get(v___x_3648_, 1);
lean_inc_ref(v_arg_3655_);
v___x_3656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3648_);
v___x_3657_ = l_Lean_Expr_isApp(v___x_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; 
lean_dec_ref(v___x_3656_);
lean_dec_ref(v_arg_3655_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
v___x_3658_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3658_;
}
else
{
lean_object* v_arg_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v_arg_3659_ = lean_ctor_get(v___x_3656_, 1);
lean_inc_ref(v_arg_3659_);
v___x_3660_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3656_);
v___x_3661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7));
v___x_3662_ = l_Lean_Expr_isConstOf(v___x_3660_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; uint8_t v___x_3664_; 
lean_dec_ref(v_arg_3655_);
v___x_3663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5));
v___x_3664_ = l_Lean_Expr_isConstOf(v___x_3660_, v___x_3663_);
lean_dec_ref(v___x_3660_);
if (v___x_3664_ == 0)
{
lean_object* v___x_3665_; 
lean_dec_ref(v_arg_3659_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
v___x_3665_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3665_;
}
else
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3659_, v_a_3623_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = l_Lean_Expr_cleanupAnnotations(v_a_3667_);
v___x_3669_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg___closed__1));
v___x_3670_ = l_Lean_Expr_isConstOf(v___x_3668_, v___x_3669_);
if (v___x_3670_ == 0)
{
uint8_t v___x_3671_; 
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
v___x_3671_ = l_Lean_Expr_isApp(v___x_3668_);
if (v___x_3671_ == 0)
{
lean_dec_ref(v___x_3668_);
lean_dec_ref(v_origExpr_3613_);
goto v___jp_3627_;
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3672_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3668_);
v___x_3673_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1));
v___x_3674_ = l_Lean_Expr_isConstOf(v___x_3672_, v___x_3673_);
lean_dec_ref(v___x_3672_);
if (v___x_3674_ == 0)
{
lean_dec_ref(v_origExpr_3613_);
goto v___jp_3627_;
}
else
{
lean_object* v___x_3675_; 
v___x_3675_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3675_;
}
}
}
else
{
uint8_t v___x_3676_; lean_object* v___x_3677_; 
lean_dec_ref(v___x_3668_);
v___x_3676_ = 2;
v___x_3677_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_3647_, v_arg_3641_, v___x_3676_, v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3677_;
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
v_a_3678_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3666_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3666_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
else
{
lean_object* v___x_3686_; 
lean_dec_ref(v___x_3660_);
lean_dec_ref(v_arg_3659_);
lean_inc_ref(v_arg_3655_);
v___x_3686_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_3655_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3742_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3742_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3742_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
if (lean_obj_tag(v_a_3687_) == 1)
{
lean_object* v_val_3691_; lean_object* v___x_3692_; 
lean_del_object(v___x_3689_);
v_val_3691_ = lean_ctor_get(v_a_3687_, 0);
lean_inc(v_val_3691_);
lean_dec_ref_known(v_a_3687_, 1);
lean_inc_ref(v_arg_3647_);
v___x_3692_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_3647_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3737_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3695_ = v___x_3692_;
v_isShared_3696_ = v_isSharedCheck_3737_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3692_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3737_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
if (lean_obj_tag(v_a_3693_) == 1)
{
lean_object* v_val_3697_; lean_object* v___x_3698_; 
lean_del_object(v___x_3695_);
v_val_3697_ = lean_ctor_get(v_a_3693_, 0);
lean_inc(v_val_3697_);
lean_dec_ref_known(v_a_3693_, 1);
lean_inc_ref(v_arg_3641_);
v___x_3698_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_3641_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3732_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3732_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3732_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
if (lean_obj_tag(v_a_3699_) == 1)
{
lean_object* v_val_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3727_; 
lean_del_object(v___x_3701_);
v_val_3703_ = lean_ctor_get(v_a_3699_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_a_3699_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3705_ = v_a_3699_;
v_isShared_3706_ = v_isSharedCheck_3727_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_val_3703_);
lean_dec(v_a_3699_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3727_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(v_val_3691_, v_val_3697_, v_val_3703_, v_arg_3655_, v_arg_3647_, v_arg_3641_, v_origExpr_3613_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3718_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3710_ = v___x_3707_;
v_isShared_3711_ = v_isSharedCheck_3718_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3707_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3718_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v_a_3708_);
v___x_3713_ = v___x_3705_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3715_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3713_);
v___x_3715_ = v___x_3710_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_del_object(v___x_3705_);
v_a_3719_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3707_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3707_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
lean_dec(v_a_3699_);
lean_dec(v_val_3697_);
lean_dec(v_val_3691_);
lean_dec_ref(v_arg_3655_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
v___x_3728_ = lean_box(0);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3728_);
v___x_3730_ = v___x_3701_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_dec(v_val_3697_);
lean_dec(v_val_3691_);
lean_dec_ref(v_arg_3655_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
return v___x_3698_;
}
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_dec(v_a_3693_);
lean_dec(v_val_3691_);
lean_dec_ref(v_arg_3655_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
v___x_3733_ = lean_box(0);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v___x_3733_);
v___x_3735_ = v___x_3695_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
lean_dec(v_val_3691_);
lean_dec_ref(v_arg_3655_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
return v___x_3692_;
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3740_; 
lean_dec(v_a_3687_);
lean_dec_ref(v_arg_3655_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
v___x_3738_ = lean_box(0);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3738_);
v___x_3740_ = v___x_3689_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_dec_ref(v_arg_3655_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
return v___x_3686_;
}
}
}
}
}
else
{
uint8_t v___x_3743_; lean_object* v___x_3744_; 
lean_dec_ref(v___x_3648_);
v___x_3743_ = 0;
v___x_3744_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_3647_, v_arg_3641_, v___x_3743_, v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3744_;
}
}
else
{
uint8_t v___x_3745_; lean_object* v___x_3746_; 
lean_dec_ref(v___x_3648_);
v___x_3745_ = 1;
v___x_3746_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_3647_, v_arg_3641_, v___x_3745_, v_origExpr_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
return v___x_3746_;
}
}
}
else
{
lean_object* v___x_3747_; 
lean_dec_ref(v___x_3642_);
lean_inc_ref(v_arg_3641_);
v___x_3747_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_3641_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3781_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3781_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3781_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
if (lean_obj_tag(v_a_3748_) == 1)
{
lean_object* v_val_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3776_; 
lean_del_object(v___x_3750_);
v_val_3752_ = lean_ctor_get(v_a_3748_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_a_3748_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3754_ = v_a_3748_;
v_isShared_3755_ = v_isSharedCheck_3776_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_val_3752_);
lean_dec(v_a_3748_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3776_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_val_3752_, v_arg_3641_, v_origExpr_3613_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3767_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3767_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v_a_3757_);
v___x_3762_ = v___x_3754_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3764_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3762_);
v___x_3764_ = v___x_3759_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_del_object(v___x_3754_);
v_a_3768_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3756_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3756_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3779_; 
lean_dec(v_a_3748_);
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
v___x_3777_ = lean_box(0);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3777_);
v___x_3779_ = v___x_3750_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_dec_ref(v_arg_3641_);
lean_dec_ref(v_origExpr_3613_);
return v___x_3747_;
}
}
}
}
else
{
lean_object* v___x_3782_; 
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_origExpr_3613_);
v___x_3782_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v___x_3638_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3791_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3791_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3791_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3787_, 0, v_a_3783_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3787_);
v___x_3789_ = v___x_3785_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
v_a_3792_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3782_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3782_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
else
{
uint8_t v___x_3800_; lean_object* v___x_3801_; 
lean_dec_ref(v___x_3634_);
lean_dec_ref(v_origExpr_3613_);
v___x_3800_ = 0;
v___x_3801_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v___x_3800_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3810_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3810_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3810_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3808_; 
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v_a_3802_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3806_);
v___x_3808_ = v___x_3804_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_a_3811_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3801_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3801_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec_ref(v_origExpr_3613_);
v_a_3819_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3632_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3632_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v_origExpr_3613_);
v_a_3827_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3631_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3631_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
v___jp_3627_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = lean_box(0);
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
return v___x_3629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(lean_object* v_t_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(v_t_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3883_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3852_ = v___x_3849_;
v_isShared_3853_ = v_isSharedCheck_3883_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3849_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3883_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
if (lean_obj_tag(v_a_3850_) == 1)
{
lean_object* v_val_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3878_; 
lean_del_object(v___x_3852_);
v_val_3854_ = lean_ctor_get(v_a_3850_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3850_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3856_ = v_a_3850_;
v_isShared_3857_ = v_isSharedCheck_3878_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_val_3854_);
lean_dec(v_a_3850_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3878_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_3854_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3869_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3861_ = v___x_3858_;
v_isShared_3862_ = v_isSharedCheck_3869_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3858_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3869_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_a_3859_);
v___x_3864_ = v___x_3856_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3866_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3864_);
v___x_3866_ = v___x_3861_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_del_object(v___x_3856_);
v_a_3870_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3858_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3858_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
lean_dec(v_a_3850_);
v___x_3879_ = lean_box(0);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 0, v___x_3879_);
v___x_3881_ = v___x_3852_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
v_a_3884_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3849_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3849_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object* v_e_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v___y_3907_; lean_object* v___x_3930_; lean_object* v_bvLogicalCache_3931_; lean_object* v___x_3932_; 
v___x_3930_ = lean_st_ref_get(v_a_3893_);
v_bvLogicalCache_3931_ = lean_ctor_get(v___x_3930_, 3);
lean_inc_ref(v_bvLogicalCache_3931_);
lean_dec(v___x_3930_);
v___x_3932_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg(v_bvLogicalCache_3931_, v_e_3892_);
lean_dec_ref(v_bvLogicalCache_3931_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v___x_3933_; 
lean_inc_ref(v_e_3892_);
v___x_3933_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_e_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
if (lean_obj_tag(v_a_3934_) == 0)
{
lean_object* v___x_3935_; 
lean_dec_ref_known(v___x_3933_, 1);
lean_inc_ref(v_e_3892_);
v___x_3935_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(v_e_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
v___y_3907_ = v___x_3935_;
goto v___jp_3906_;
}
else
{
v___y_3907_ = v___x_3933_;
goto v___jp_3906_;
}
}
else
{
v___y_3907_ = v___x_3933_;
goto v___jp_3906_;
}
}
else
{
lean_object* v_val_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec_ref(v_e_3892_);
v_val_3936_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3932_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_val_3936_);
lean_dec(v___x_3932_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
lean_ctor_set_tag(v___x_3938_, 0);
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_val_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
v___jp_3906_:
{
if (lean_obj_tag(v___y_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3929_; 
v_a_3908_ = lean_ctor_get(v___y_3907_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___y_3907_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3910_ = v___y_3907_;
v_isShared_3911_ = v_isSharedCheck_3929_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___y_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3929_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v_lemmas_3913_; lean_object* v_bvExprCache_3914_; lean_object* v_bvPredCache_3915_; lean_object* v_bvLogicalCache_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3928_; 
v___x_3912_ = lean_st_ref_take(v_a_3893_);
v_lemmas_3913_ = lean_ctor_get(v___x_3912_, 0);
v_bvExprCache_3914_ = lean_ctor_get(v___x_3912_, 1);
v_bvPredCache_3915_ = lean_ctor_get(v___x_3912_, 2);
v_bvLogicalCache_3916_ = lean_ctor_get(v___x_3912_, 3);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3918_ = v___x_3912_;
v_isShared_3919_ = v_isSharedCheck_3928_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_bvLogicalCache_3916_);
lean_inc(v_bvPredCache_3915_);
lean_inc(v_bvExprCache_3914_);
lean_inc(v_lemmas_3913_);
lean_dec(v___x_3912_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3928_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_inc(v_a_3908_);
v___x_3920_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17___redArg(v_bvLogicalCache_3916_, v_e_3892_, v_a_3908_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 3, v___x_3920_);
v___x_3922_ = v___x_3918_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_lemmas_3913_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_bvExprCache_3914_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_bvPredCache_3915_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3923_ = lean_st_ref_put(v_a_3893_, v___x_3922_);
if (v_isShared_3911_ == 0)
{
v___x_3925_ = v___x_3910_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3908_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3892_);
return v___y_3907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(lean_object* v_origExpr_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_origExpr_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(lean_object* v_origExpr_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_spec__6(lean_object* v_as_3974_, size_t v_i_3975_, size_t v_stop_3976_, lean_object* v_b_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_a_3992_; uint8_t v___x_3996_; 
v___x_3996_ = lean_usize_dec_eq(v_i_3975_, v_stop_3976_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; lean_object* v___y_3999_; lean_object* v___x_4053_; 
v___x_3997_ = lean_array_uget_borrowed(v_as_3974_, v_i_3975_);
lean_inc(v___x_3997_);
v___x_4053_ = l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(v___x_3997_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4055_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___x_4053_, 1);
v___x_4055_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v___x_3997_, v___y_3980_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; uint8_t v___x_4057_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
v___x_4057_ = lean_unbox(v_a_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; 
lean_dec_ref_known(v___x_4055_, 1);
v___x_4058_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v_a_4054_, v___y_3980_);
lean_dec(v_a_4054_);
v___y_3999_ = v___x_4058_;
goto v___jp_3998_;
}
else
{
lean_dec(v_a_4054_);
v___y_3999_ = v___x_4055_;
goto v___jp_3998_;
}
}
else
{
lean_dec(v_a_4054_);
v___y_3999_ = v___x_4055_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
v_a_4059_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4053_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4053_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
v___jp_3998_:
{
if (lean_obj_tag(v___y_3999_) == 0)
{
lean_object* v_a_4000_; uint8_t v___x_4001_; 
v_a_4000_ = lean_ctor_get(v___y_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___y_3999_, 1);
v___x_4001_ = lean_unbox(v_a_4000_);
lean_dec(v_a_4000_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; 
lean_inc(v___x_3997_);
v___x_4002_ = l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg(v___x_3997_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v___x_4002_, 1);
if (lean_obj_tag(v_a_4003_) == 1)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_dec_ref_known(v_a_4003_, 1);
v___x_4004_ = lean_box(0);
lean_inc(v___x_3997_);
v___x_4005_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v___x_3997_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_dec_ref_known(v___x_4005_, 1);
v_a_3992_ = v___x_4004_;
goto v___jp_3991_;
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v___x_4014_; 
lean_dec(v_a_4003_);
lean_inc(v___x_3997_);
v___x_4014_ = l_Lean_Meta_Tactic_BVDecide_isValidBoolAtom___redArg(v___x_3997_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; uint8_t v___x_4016_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4014_, 1);
v___x_4016_ = lean_unbox(v_a_4015_);
lean_dec(v_a_4015_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4017_; 
v___x_4017_ = lean_box(0);
v_a_3992_ = v___x_4017_;
goto v___jp_3991_;
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = lean_box(0);
lean_inc(v___x_3997_);
v___x_4019_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v___x_3997_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_dec_ref_known(v___x_4019_, 1);
v_a_3992_ = v___x_4018_;
goto v___jp_3991_;
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4014_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4014_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
v_a_4036_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4002_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4002_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_box(0);
v_a_3992_ = v___x_4044_;
goto v___jp_3991_;
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
v_a_4045_ = lean_ctor_get(v___y_3999_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___y_3999_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___y_3999_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___y_3999_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
else
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v_b_3977_);
return v___x_4067_;
}
v___jp_3991_:
{
size_t v___x_3993_; size_t v___x_3994_; 
v___x_3993_ = ((size_t)1ULL);
v___x_3994_ = lean_usize_add(v_i_3975_, v___x_3993_);
v_i_3975_ = v___x_3994_;
v_b_3977_ = v_a_3992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom(lean_object* v_e_4068_, lean_object* v_width_4069_, uint8_t v_synthetic_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v___x_4084_; 
lean_inc_ref(v_e_4068_);
v___x_4084_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_checkTheoryAtom(v_synthetic_4070_, v_e_4068_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4086_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
lean_inc(v_width_4069_);
v___x_4086_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(v_e_4068_, v_width_4069_, v_synthetic_4070_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc_n(v_a_4087_, 2);
lean_dec_ref_known(v___x_4086_, 1);
v___x_4088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__2);
lean_inc(v_width_4069_);
v___x_4089_ = l_Lean_mkNatLit(v_width_4069_);
v___x_4090_ = l_Lean_mkNatLit(v_a_4087_);
v___x_4091_ = l_Lean_mkAppB(v___x_4088_, v___x_4089_, v___x_4090_);
v___x_4092_ = l_Lean_Meta_Sym_shareCommonInc(v___x_4091_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4135_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4135_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4135_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___f_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___y_4101_; lean_object* v___x_4118_; lean_object* v___x_4119_; uint8_t v___x_4120_; 
v___f_4097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___closed__3));
lean_inc(v_width_4069_);
v___x_4098_ = l_Std_Tactic_BVDecide_BVExpr_var___override(v_width_4069_, v_a_4087_);
lean_inc(v_a_4093_);
v___x_4099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4099_, 0, v_width_4069_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
lean_ctor_set(v___x_4099_, 2, v_a_4093_);
lean_ctor_set(v___x_4099_, 3, v___f_4097_);
lean_ctor_set(v___x_4099_, 4, v_a_4093_);
v___x_4118_ = lean_unsigned_to_nat(0u);
v___x_4119_ = lean_array_get_size(v_a_4085_);
v___x_4120_ = lean_nat_dec_lt(v___x_4118_, v___x_4119_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4122_; 
lean_dec(v_a_4085_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4099_);
v___x_4122_ = v___x_4095_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4099_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
else
{
lean_object* v___x_4124_; uint8_t v___x_4125_; 
v___x_4124_ = lean_box(0);
v___x_4125_ = lean_nat_dec_le(v___x_4119_, v___x_4119_);
if (v___x_4125_ == 0)
{
if (v___x_4120_ == 0)
{
lean_object* v___x_4127_; 
lean_dec(v_a_4085_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4099_);
v___x_4127_ = v___x_4095_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4099_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
else
{
size_t v___x_4129_; size_t v___x_4130_; lean_object* v___x_4131_; 
lean_del_object(v___x_4095_);
v___x_4129_ = ((size_t)0ULL);
v___x_4130_ = lean_usize_of_nat(v___x_4119_);
v___x_4131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_spec__6(v_a_4085_, v___x_4129_, v___x_4130_, v___x_4124_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4085_);
v___y_4101_ = v___x_4131_;
goto v___jp_4100_;
}
}
else
{
size_t v___x_4132_; size_t v___x_4133_; lean_object* v___x_4134_; 
lean_del_object(v___x_4095_);
v___x_4132_ = ((size_t)0ULL);
v___x_4133_ = lean_usize_of_nat(v___x_4119_);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_spec__6(v_a_4085_, v___x_4132_, v___x_4133_, v___x_4124_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4085_);
v___y_4101_ = v___x_4134_;
goto v___jp_4100_;
}
}
v___jp_4100_:
{
if (lean_obj_tag(v___y_4101_) == 0)
{
lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_isSharedCheck_4108_ = !lean_is_exclusive(v___y_4101_);
if (v_isSharedCheck_4108_ == 0)
{
lean_object* v_unused_4109_; 
v_unused_4109_ = lean_ctor_get(v___y_4101_, 0);
lean_dec(v_unused_4109_);
v___x_4103_ = v___y_4101_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_dec(v___y_4101_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4099_);
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4099_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_dec_ref_known(v___x_4099_, 5);
v_a_4110_ = lean_ctor_get(v___y_4101_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___y_4101_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___y_4101_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___y_4101_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_a_4087_);
lean_dec(v_a_4085_);
lean_dec(v_width_4069_);
v_a_4136_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4092_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4092_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec(v_a_4085_);
lean_dec(v_width_4069_);
v_a_4144_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4086_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4086_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec(v_width_4069_);
lean_dec_ref(v_e_4068_);
v_a_4152_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4084_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4084_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(lean_object* v_e_4160_, uint8_t v_synthetic_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___x_4175_; 
lean_inc_ref(v_e_4160_);
v___x_4175_ = l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg(v_e_4160_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4209_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4209_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4209_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
if (lean_obj_tag(v_a_4176_) == 1)
{
lean_object* v_val_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4204_; 
lean_del_object(v___x_4178_);
v_val_4180_ = lean_ctor_get(v_a_4176_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_a_4176_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4182_ = v_a_4176_;
v_isShared_4183_ = v_isSharedCheck_4204_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_val_4180_);
lean_dec(v_a_4176_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4204_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; 
v___x_4184_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom(v_e_4160_, v_val_4180_, v_synthetic_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4195_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4187_ = v___x_4184_;
v_isShared_4188_ = v_isSharedCheck_4195_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4184_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4195_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v_a_4185_);
v___x_4190_ = v___x_4182_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4192_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 0, v___x_4190_);
v___x_4192_ = v___x_4187_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_del_object(v___x_4182_);
v_a_4196_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4184_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4184_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
}
else
{
lean_object* v___x_4205_; lean_object* v___x_4207_; 
lean_dec(v_a_4176_);
lean_dec_ref(v_e_4160_);
v___x_4205_ = lean_box(0);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4205_);
v___x_4207_ = v___x_4178_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_dec_ref(v_e_4160_);
v_a_4210_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4175_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4175_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5(void){
_start:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4233_ = lean_box(0);
v___x_4234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4));
v___x_4235_ = l_Lean_mkConst(v___x_4234_, v___x_4233_);
return v___x_4235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3(void){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4243_ = lean_box(0);
v___x_4244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2));
v___x_4245_ = l_Lean_mkConst(v___x_4244_, v___x_4243_);
return v___x_4245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6(void){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = lean_box(0);
v___x_4253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_4254_ = l_Lean_mkConst(v___x_4253_, v___x_4252_);
return v___x_4254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9(void){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = lean_box(0);
v___x_4262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_4263_ = l_Lean_mkConst(v___x_4262_, v___x_4261_);
return v___x_4263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12(void){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4271_ = lean_box(0);
v___x_4272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_4273_ = l_Lean_mkConst(v___x_4272_, v___x_4271_);
return v___x_4273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15(void){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4280_ = lean_box(0);
v___x_4281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14));
v___x_4282_ = l_Lean_mkConst(v___x_4281_, v___x_4280_);
return v___x_4282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = lean_box(0);
v___x_4290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17));
v___x_4291_ = l_Lean_mkConst(v___x_4290_, v___x_4289_);
return v___x_4291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21(void){
_start:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4298_ = lean_box(0);
v___x_4299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20));
v___x_4300_ = l_Lean_mkConst(v___x_4299_, v___x_4298_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(lean_object* v_innerExpr_4301_, lean_object* v_op_4302_, lean_object* v_congrThm_4303_, lean_object* v_origExpr_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_){
_start:
{
lean_object* v___x_4318_; 
lean_inc_ref(v_innerExpr_4301_);
v___x_4318_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4301_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4381_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4381_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4381_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
if (lean_obj_tag(v_a_4319_) == 1)
{
lean_object* v_val_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4376_; 
lean_del_object(v___x_4321_);
v_val_4323_ = lean_ctor_get(v_a_4319_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v_a_4319_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4325_ = v_a_4319_;
v_isShared_4326_ = v_isSharedCheck_4376_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_val_4323_);
lean_dec(v_a_4319_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4376_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v_width_4327_; lean_object* v_bvExpr_4328_; lean_object* v_expr_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___y_4335_; 
v_width_4327_ = lean_ctor_get(v_val_4323_, 0);
lean_inc_n(v_width_4327_, 3);
v_bvExpr_4328_ = lean_ctor_get(v_val_4323_, 1);
v_expr_4329_ = lean_ctor_get(v_val_4323_, 4);
lean_inc_ref(v_bvExpr_4328_);
lean_inc(v_op_4302_);
v___x_4330_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_4327_, v_op_4302_, v_bvExpr_4328_);
v___x_4331_ = lean_box(0);
v___x_4332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5);
v___x_4333_ = l_Lean_mkNatLit(v_width_4327_);
switch(lean_obj_tag(v_op_4302_))
{
case 0:
{
lean_object* v___x_4360_; 
v___x_4360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3);
v___y_4335_ = v___x_4360_;
goto v___jp_4334_;
}
case 1:
{
lean_object* v_n_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v_n_4361_ = lean_ctor_get(v_op_4302_, 0);
lean_inc(v_n_4361_);
lean_dec_ref_known(v_op_4302_, 1);
v___x_4362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6);
v___x_4363_ = l_Lean_mkNatLit(v_n_4361_);
v___x_4364_ = l_Lean_Expr_app___override(v___x_4362_, v___x_4363_);
v___y_4335_ = v___x_4364_;
goto v___jp_4334_;
}
case 2:
{
lean_object* v_n_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v_n_4365_ = lean_ctor_get(v_op_4302_, 0);
lean_inc(v_n_4365_);
lean_dec_ref_known(v_op_4302_, 1);
v___x_4366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9);
v___x_4367_ = l_Lean_mkNatLit(v_n_4365_);
v___x_4368_ = l_Lean_Expr_app___override(v___x_4366_, v___x_4367_);
v___y_4335_ = v___x_4368_;
goto v___jp_4334_;
}
case 3:
{
lean_object* v_n_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v_n_4369_ = lean_ctor_get(v_op_4302_, 0);
lean_inc(v_n_4369_);
lean_dec_ref_known(v_op_4302_, 1);
v___x_4370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12);
v___x_4371_ = l_Lean_mkNatLit(v_n_4369_);
v___x_4372_ = l_Lean_Expr_app___override(v___x_4370_, v___x_4371_);
v___y_4335_ = v___x_4372_;
goto v___jp_4334_;
}
case 4:
{
lean_object* v___x_4373_; 
v___x_4373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15);
v___y_4335_ = v___x_4373_;
goto v___jp_4334_;
}
case 5:
{
lean_object* v___x_4374_; 
v___x_4374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18);
v___y_4335_ = v___x_4374_;
goto v___jp_4334_;
}
default: 
{
lean_object* v___x_4375_; 
v___x_4375_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21);
v___y_4335_ = v___x_4375_;
goto v___jp_4334_;
}
}
v___jp_4334_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; 
lean_inc_ref(v_expr_4329_);
v___x_4336_ = l_Lean_mkApp3(v___x_4332_, v___x_4333_, v___y_4335_, v_expr_4329_);
v___x_4337_ = l_Lean_Meta_Sym_shareCommonInc(v___x_4336_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4351_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4340_ = v___x_4337_;
v_isShared_4341_ = v_isSharedCheck_4351_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4337_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4351_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4342_ = l_Lean_mkConst(v_congrThm_4303_, v___x_4331_);
v___x_4343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed), 15, 3);
lean_closure_set(v___x_4343_, 0, v_val_4323_);
lean_closure_set(v___x_4343_, 1, v_innerExpr_4301_);
lean_closure_set(v___x_4343_, 2, v___x_4342_);
v___x_4344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4344_, 0, v_width_4327_);
lean_ctor_set(v___x_4344_, 1, v___x_4330_);
lean_ctor_set(v___x_4344_, 2, v_origExpr_4304_);
lean_ctor_set(v___x_4344_, 3, v___x_4343_);
lean_ctor_set(v___x_4344_, 4, v_a_4338_);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v___x_4344_);
v___x_4346_ = v___x_4325_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4344_);
v___x_4346_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4348_; 
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v___x_4346_);
v___x_4348_ = v___x_4340_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v___x_4346_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec_ref(v___x_4330_);
lean_dec(v_width_4327_);
lean_del_object(v___x_4325_);
lean_dec(v_val_4323_);
lean_dec_ref(v_origExpr_4304_);
lean_dec(v_congrThm_4303_);
lean_dec_ref(v_innerExpr_4301_);
v_a_4352_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4337_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4337_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
}
else
{
lean_object* v___x_4377_; lean_object* v___x_4379_; 
lean_dec(v_a_4319_);
lean_dec_ref(v_origExpr_4304_);
lean_dec(v_congrThm_4303_);
lean_dec(v_op_4302_);
lean_dec_ref(v_innerExpr_4301_);
v___x_4377_ = lean_box(0);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v___x_4377_);
v___x_4379_ = v___x_4321_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_4304_);
lean_dec(v_congrThm_4303_);
lean_dec(v_op_4302_);
lean_dec_ref(v_innerExpr_4301_);
return v___x_4318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object* v_distance_4390_, lean_object* v_innerExpr_4391_, lean_object* v_shiftOp_4392_, lean_object* v_shiftOpName_4393_, lean_object* v_congrThm_4394_, lean_object* v_origExpr_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v___x_4409_; 
lean_inc_ref(v_innerExpr_4391_);
v___x_4409_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4391_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4459_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4459_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4459_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
if (lean_obj_tag(v_a_4410_) == 1)
{
lean_object* v_val_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4454_; 
lean_del_object(v___x_4412_);
v_val_4414_ = lean_ctor_get(v_a_4410_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_a_4410_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4416_ = v_a_4410_;
v_isShared_4417_ = v_isSharedCheck_4454_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_val_4414_);
lean_dec(v_a_4410_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4454_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v_width_4418_; lean_object* v_bvExpr_4419_; lean_object* v_expr_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v_width_4418_ = lean_ctor_get(v_val_4414_, 0);
lean_inc_n(v_width_4418_, 3);
v_bvExpr_4419_ = lean_ctor_get(v_val_4414_, 1);
v_expr_4420_ = lean_ctor_get(v_val_4414_, 4);
lean_inc(v_distance_4390_);
v___x_4421_ = lean_apply_1(v_shiftOp_4392_, v_distance_4390_);
lean_inc_ref(v_bvExpr_4419_);
v___x_4422_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_4418_, v___x_4421_, v_bvExpr_4419_);
v___x_4423_ = lean_box(0);
v___x_4424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5);
v___x_4425_ = l_Lean_mkNatLit(v_width_4418_);
v___x_4426_ = l_Lean_mkConst(v_shiftOpName_4393_, v___x_4423_);
v___x_4427_ = l_Lean_mkNatLit(v_distance_4390_);
lean_inc_ref(v___x_4427_);
v___x_4428_ = l_Lean_Expr_app___override(v___x_4426_, v___x_4427_);
lean_inc_ref(v_expr_4420_);
v___x_4429_ = l_Lean_mkApp3(v___x_4424_, v___x_4425_, v___x_4428_, v_expr_4420_);
v___x_4430_ = l_Lean_Meta_Sym_shareCommonInc(v___x_4429_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4445_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4445_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4445_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4435_ = l_Lean_mkConst(v_congrThm_4394_, v___x_4423_);
v___x_4436_ = l_Lean_Expr_app___override(v___x_4435_, v___x_4427_);
v___x_4437_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed), 15, 3);
lean_closure_set(v___x_4437_, 0, v_val_4414_);
lean_closure_set(v___x_4437_, 1, v_innerExpr_4391_);
lean_closure_set(v___x_4437_, 2, v___x_4436_);
v___x_4438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4438_, 0, v_width_4418_);
lean_ctor_set(v___x_4438_, 1, v___x_4422_);
lean_ctor_set(v___x_4438_, 2, v_origExpr_4395_);
lean_ctor_set(v___x_4438_, 3, v___x_4437_);
lean_ctor_set(v___x_4438_, 4, v_a_4431_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4438_);
v___x_4440_ = v___x_4416_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4438_);
v___x_4440_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
lean_object* v___x_4442_; 
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4440_);
v___x_4442_ = v___x_4433_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
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
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec_ref(v___x_4427_);
lean_dec_ref(v___x_4422_);
lean_dec(v_width_4418_);
lean_del_object(v___x_4416_);
lean_dec(v_val_4414_);
lean_dec_ref(v_origExpr_4395_);
lean_dec(v_congrThm_4394_);
lean_dec_ref(v_innerExpr_4391_);
v_a_4446_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4430_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4430_);
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
else
{
lean_object* v___x_4455_; lean_object* v___x_4457_; 
lean_dec(v_a_4410_);
lean_dec_ref(v_origExpr_4395_);
lean_dec(v_congrThm_4394_);
lean_dec(v_shiftOpName_4393_);
lean_dec_ref(v_shiftOp_4392_);
lean_dec_ref(v_innerExpr_4391_);
lean_dec(v_distance_4390_);
v___x_4455_ = lean_box(0);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4455_);
v___x_4457_ = v___x_4412_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4455_);
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
lean_dec_ref(v_origExpr_4395_);
lean_dec(v_congrThm_4394_);
lean_dec(v_shiftOpName_4393_);
lean_dec_ref(v_shiftOp_4392_);
lean_dec_ref(v_innerExpr_4391_);
lean_dec(v_distance_4390_);
return v___x_4409_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88(void){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4466_ = lean_box(0);
v___x_4467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87));
v___x_4468_ = l_Lean_mkConst(v___x_4467_, v___x_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(lean_object* v_distanceExpr_4477_, lean_object* v_innerExpr_4478_, lean_object* v_rotateOp_4479_, lean_object* v_rotateOpName_4480_, lean_object* v_congrThm_4481_, lean_object* v_origExpr_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_Meta_Sym_getNatValue_x3f(v_distanceExpr_4477_);
if (lean_obj_tag(v___x_4496_) == 1)
{
lean_object* v_val_4497_; lean_object* v___x_4498_; 
v_val_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_val_4497_);
lean_dec_ref_known(v___x_4496_, 1);
v___x_4498_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_4497_, v_innerExpr_4478_, v_rotateOp_4479_, v_rotateOpName_4480_, v_congrThm_4481_, v_origExpr_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
return v___x_4498_;
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
lean_dec(v___x_4496_);
lean_dec_ref(v_origExpr_4482_);
lean_dec(v_congrThm_4481_);
lean_dec(v_rotateOpName_4480_);
lean_dec_ref(v_rotateOp_4479_);
lean_dec_ref(v_innerExpr_4478_);
v___x_4499_ = lean_box(0);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
return v___x_4500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(lean_object* v_x_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_){
_start:
{
lean_object* v___x_4523_; 
lean_inc_ref(v_x_4509_);
v___x_4523_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_x_4509_);
if (lean_obj_tag(v___x_4523_) == 1)
{
lean_object* v_val_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v_x_4509_);
v_val_4524_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4526_ = v___x_4523_;
v_isShared_4527_ = v_isSharedCheck_4550_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_val_4524_);
lean_dec(v___x_4523_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4550_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v_n_4528_; lean_object* v_val_4529_; lean_object* v___x_4530_; 
v_n_4528_ = lean_ctor_get(v_val_4524_, 0);
lean_inc(v_n_4528_);
v_val_4529_ = lean_ctor_get(v_val_4524_, 1);
lean_inc(v_val_4529_);
lean_dec(v_val_4524_);
v___x_4530_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_n_4528_, v_val_4529_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4541_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4533_ = v___x_4530_;
v_isShared_4534_ = v_isSharedCheck_4541_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4530_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4541_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v_a_4531_);
v___x_4536_ = v___x_4526_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
lean_object* v___x_4538_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 0, v___x_4536_);
v___x_4538_ = v___x_4533_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
lean_del_object(v___x_4526_);
v_a_4542_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4530_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4530_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
}
else
{
uint8_t v___x_4551_; lean_object* v___x_4552_; 
lean_dec(v___x_4523_);
v___x_4551_ = 0;
v___x_4552_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_x_4509_, v___x_4551_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
return v___x_4552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(lean_object* v_origExpr_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v___f_4606_; lean_object* v___f_4607_; lean_object* v___f_4608_; lean_object* v___f_4609_; lean_object* v___f_4610_; lean_object* v___f_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___f_4606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0));
v___f_4607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1));
v___f_4608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2));
v___f_4609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3));
v___f_4610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4));
v___f_4611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5));
v___x_4612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0));
v___x_4613_ = l_Lean_Core_checkSystem(v___x_4612_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v___x_4614_; 
lean_dec_ref_known(v___x_4613_, 1);
lean_inc_ref(v_origExpr_4577_);
v___x_4614_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_4577_, v_a_4587_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_5102_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_5102_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_5102_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; uint8_t v___x_4620_; 
v___x_4619_ = l_Lean_Expr_cleanupAnnotations(v_a_4615_);
v___x_4620_ = l_Lean_Expr_isApp(v___x_4619_);
if (v___x_4620_ == 0)
{
lean_dec_ref(v___x_4619_);
lean_del_object(v___x_4617_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4603_;
}
else
{
lean_object* v_arg_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; 
v_arg_4621_ = lean_ctor_get(v___x_4619_, 1);
lean_inc_ref(v_arg_4621_);
v___x_4622_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4619_);
v___x_4623_ = l_Lean_Expr_isApp(v___x_4622_);
if (v___x_4623_ == 0)
{
lean_dec_ref(v___x_4622_);
lean_dec_ref(v_arg_4621_);
lean_del_object(v___x_4617_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4603_;
}
else
{
lean_object* v_arg_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v_arg_4624_ = lean_ctor_get(v___x_4622_, 1);
lean_inc_ref(v_arg_4624_);
v___x_4625_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4622_);
v___x_4626_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__0));
v___x_4627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6));
v___x_4628_ = l_Lean_Expr_isConstOf(v___x_4625_, v___x_4627_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4629_; uint8_t v___x_4630_; 
v___x_4629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7));
v___x_4630_ = l_Lean_Expr_isConstOf(v___x_4625_, v___x_4629_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8));
v___x_4632_ = l_Lean_Expr_isConstOf(v___x_4625_, v___x_4631_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10));
v___x_4634_ = l_Lean_Expr_isConstOf(v___x_4625_, v___x_4633_);
if (v___x_4634_ == 0)
{
uint8_t v___x_4635_; 
v___x_4635_ = l_Lean_Expr_isApp(v___x_4625_);
if (v___x_4635_ == 0)
{
lean_dec_ref(v___x_4625_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_del_object(v___x_4617_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4603_;
}
else
{
lean_object* v_arg_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; 
v_arg_4636_ = lean_ctor_get(v___x_4625_, 1);
lean_inc_ref(v_arg_4636_);
v___x_4637_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4625_);
v___x_4638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11));
v___x_4639_ = l_Lean_Expr_isConstOf(v___x_4637_, v___x_4638_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; uint8_t v___x_4641_; 
v___x_4640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12));
v___x_4641_ = l_Lean_Expr_isConstOf(v___x_4637_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_object* v___x_4642_; uint8_t v___x_4643_; 
v___x_4642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14));
v___x_4643_ = l_Lean_Expr_isConstOf(v___x_4637_, v___x_4642_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; uint8_t v___x_4645_; 
v___x_4644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16));
v___x_4645_ = l_Lean_Expr_isConstOf(v___x_4637_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; uint8_t v___x_4647_; 
v___x_4646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19));
v___x_4647_ = l_Lean_Expr_isConstOf(v___x_4637_, v___x_4646_);
if (v___x_4647_ == 0)
{
uint8_t v___x_4648_; 
v___x_4648_ = l_Lean_Expr_isApp(v___x_4637_);
if (v___x_4648_ == 0)
{
lean_dec_ref(v___x_4637_);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_del_object(v___x_4617_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4603_;
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v___x_4649_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4637_);
v___x_4650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7));
v___x_4651_ = l_Lean_Expr_isConstOf(v___x_4649_, v___x_4650_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; uint8_t v___x_4653_; 
v___x_4652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21));
v___x_4653_ = l_Lean_Expr_isConstOf(v___x_4649_, v___x_4652_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; uint8_t v___x_4655_; 
lean_dec_ref(v_arg_4636_);
lean_del_object(v___x_4617_);
v___x_4654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23));
v___x_4655_ = l_Lean_Expr_isConstOf(v___x_4649_, v___x_4654_);
if (v___x_4655_ == 0)
{
uint8_t v___x_4656_; 
v___x_4656_ = l_Lean_Expr_isApp(v___x_4649_);
if (v___x_4656_ == 0)
{
lean_dec_ref(v___x_4649_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4603_;
}
else
{
lean_object* v_arg_4657_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___x_4700_; uint8_t v___x_4701_; 
v_arg_4657_ = lean_ctor_get(v___x_4649_, 1);
lean_inc_ref(v_arg_4657_);
v___x_4700_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4649_);
v___x_4701_ = l_Lean_Expr_isApp(v___x_4700_);
if (v___x_4701_ == 0)
{
lean_dec_ref(v___x_4700_);
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4603_;
}
else
{
lean_object* v_arg_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; uint8_t v___x_4705_; 
v_arg_4702_ = lean_ctor_get(v___x_4700_, 1);
lean_inc_ref(v_arg_4702_);
v___x_4703_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4700_);
v___x_4704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34));
v___x_4705_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4704_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; uint8_t v___x_4707_; 
v___x_4706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37));
v___x_4707_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40));
v___x_4709_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4708_);
if (v___x_4709_ == 0)
{
lean_object* v___x_4710_; uint8_t v___x_4711_; 
lean_dec_ref(v_arg_4702_);
lean_dec_ref(v_arg_4657_);
v___x_4710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43));
v___x_4711_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4710_);
if (v___x_4711_ == 0)
{
lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46));
v___x_4713_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; uint8_t v___x_4715_; 
v___x_4714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49));
v___x_4715_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; uint8_t v___x_4717_; 
v___x_4716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52));
v___x_4717_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4716_);
if (v___x_4717_ == 0)
{
lean_object* v___x_4718_; uint8_t v___x_4719_; 
v___x_4718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55));
v___x_4719_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4718_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; uint8_t v___x_4721_; 
v___x_4720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58));
v___x_4721_ = l_Lean_Expr_isConstOf(v___x_4703_, v___x_4720_);
lean_dec_ref(v___x_4703_);
if (v___x_4721_ == 0)
{
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4603_;
}
else
{
uint8_t v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4722_ = 0;
v___x_4723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60));
v___x_4724_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_4624_, v_arg_4621_, v___x_4722_, v___x_4723_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4724_;
}
}
else
{
uint8_t v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
lean_dec_ref(v___x_4703_);
v___x_4725_ = 2;
v___x_4726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62));
v___x_4727_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_4624_, v_arg_4621_, v___x_4725_, v___x_4726_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4727_;
}
}
else
{
uint8_t v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
lean_dec_ref(v___x_4703_);
v___x_4728_ = 3;
v___x_4729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64));
v___x_4730_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_4624_, v_arg_4621_, v___x_4728_, v___x_4729_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4730_;
}
}
else
{
uint8_t v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
lean_dec_ref(v___x_4703_);
v___x_4731_ = 4;
v___x_4732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66));
v___x_4733_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_4624_, v_arg_4621_, v___x_4731_, v___x_4732_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4733_;
}
}
else
{
uint8_t v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
lean_dec_ref(v___x_4703_);
v___x_4734_ = 5;
v___x_4735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68));
v___x_4736_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_4624_, v_arg_4621_, v___x_4734_, v___x_4735_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4736_;
}
}
else
{
uint8_t v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
lean_dec_ref(v___x_4703_);
v___x_4737_ = 6;
v___x_4738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70));
v___x_4739_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_4624_, v_arg_4621_, v___x_4737_, v___x_4738_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4739_;
}
}
else
{
lean_object* v___x_4740_; 
lean_dec_ref(v___x_4703_);
lean_inc_ref(v_arg_4621_);
lean_inc_ref(v_arg_4657_);
v___x_4740_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_4657_, v_arg_4621_, v_a_4587_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; uint8_t v___y_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref_known(v___x_4740_, 1);
v___x_4755_ = l_Lean_Expr_cleanupAnnotations(v_arg_4702_);
v___x_4756_ = l_Lean_Expr_isApp(v___x_4755_);
if (v___x_4756_ == 0)
{
lean_dec_ref(v___x_4755_);
lean_dec(v_a_4741_);
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4600_;
}
else
{
lean_object* v_arg_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; uint8_t v___x_4760_; 
v_arg_4757_ = lean_ctor_get(v___x_4755_, 1);
lean_inc_ref(v_arg_4757_);
v___x_4758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4755_);
v___x_4759_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1));
v___x_4760_ = l_Lean_Expr_isConstOf(v___x_4758_, v___x_4759_);
lean_dec_ref(v___x_4758_);
if (v___x_4760_ == 0)
{
lean_dec_ref(v_arg_4757_);
lean_dec(v_a_4741_);
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4600_;
}
else
{
lean_object* v___x_4761_; 
v___x_4761_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_4757_);
if (lean_obj_tag(v___x_4761_) == 0)
{
v___y_4754_ = v___x_4707_;
goto v___jp_4753_;
}
else
{
lean_dec_ref_known(v___x_4761_, 1);
v___y_4754_ = v___x_4760_;
goto v___jp_4753_;
}
}
}
v___jp_4742_:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72);
v___x_4744_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg(v___x_4743_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_dec_ref_known(v___x_4744_, 1);
v___y_4680_ = v_a_4578_;
v___y_4681_ = v_a_4579_;
v___y_4682_ = v_a_4580_;
v___y_4683_ = v_a_4581_;
v___y_4684_ = v_a_4582_;
v___y_4685_ = v_a_4583_;
v___y_4686_ = v_a_4584_;
v___y_4687_ = v_a_4585_;
v___y_4688_ = v_a_4586_;
v___y_4689_ = v_a_4587_;
v___y_4690_ = v_a_4588_;
v___y_4691_ = v_a_4589_;
goto v___jp_4679_;
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4744_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4744_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
v___jp_4753_:
{
if (v___y_4754_ == 0)
{
lean_dec(v_a_4741_);
v___y_4680_ = v_a_4578_;
v___y_4681_ = v_a_4579_;
v___y_4682_ = v_a_4580_;
v___y_4683_ = v_a_4581_;
v___y_4684_ = v_a_4582_;
v___y_4685_ = v_a_4583_;
v___y_4686_ = v_a_4584_;
v___y_4687_ = v_a_4585_;
v___y_4688_ = v_a_4586_;
v___y_4689_ = v_a_4587_;
v___y_4690_ = v_a_4588_;
v___y_4691_ = v_a_4589_;
goto v___jp_4679_;
}
else
{
if (lean_obj_tag(v_a_4741_) == 0)
{
if (v___x_4707_ == 0)
{
v___y_4680_ = v_a_4578_;
v___y_4681_ = v_a_4579_;
v___y_4682_ = v_a_4580_;
v___y_4683_ = v_a_4581_;
v___y_4684_ = v_a_4582_;
v___y_4685_ = v_a_4583_;
v___y_4686_ = v_a_4584_;
v___y_4687_ = v_a_4585_;
v___y_4688_ = v_a_4586_;
v___y_4689_ = v_a_4587_;
v___y_4690_ = v_a_4588_;
v___y_4691_ = v_a_4589_;
goto v___jp_4679_;
}
else
{
goto v___jp_4742_;
}
}
else
{
lean_dec_ref_known(v_a_4741_, 1);
goto v___jp_4742_;
}
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_dec_ref(v_arg_4702_);
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v_a_4762_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4740_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4740_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
}
else
{
lean_object* v___x_4770_; 
lean_dec_ref(v___x_4703_);
lean_inc_ref(v_arg_4621_);
lean_inc_ref(v_arg_4657_);
v___x_4770_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_4657_, v_arg_4621_, v_a_4587_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; uint8_t v___y_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___x_4770_, 1);
v___x_4785_ = l_Lean_Expr_cleanupAnnotations(v_arg_4702_);
v___x_4786_ = l_Lean_Expr_isApp(v___x_4785_);
if (v___x_4786_ == 0)
{
lean_dec_ref(v___x_4785_);
lean_dec(v_a_4771_);
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4594_;
}
else
{
lean_object* v_arg_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v_arg_4787_ = lean_ctor_get(v___x_4785_, 1);
lean_inc_ref(v_arg_4787_);
v___x_4788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4785_);
v___x_4789_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1));
v___x_4790_ = l_Lean_Expr_isConstOf(v___x_4788_, v___x_4789_);
lean_dec_ref(v___x_4788_);
if (v___x_4790_ == 0)
{
lean_dec_ref(v_arg_4787_);
lean_dec(v_a_4771_);
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4594_;
}
else
{
lean_object* v___x_4791_; 
v___x_4791_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_4787_);
if (lean_obj_tag(v___x_4791_) == 0)
{
v___y_4784_ = v___x_4705_;
goto v___jp_4783_;
}
else
{
lean_dec_ref_known(v___x_4791_, 1);
v___y_4784_ = v___x_4790_;
goto v___jp_4783_;
}
}
}
v___jp_4772_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72);
v___x_4774_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg(v___x_4773_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_dec_ref_known(v___x_4774_, 1);
v___y_4659_ = v_a_4578_;
v___y_4660_ = v_a_4579_;
v___y_4661_ = v_a_4580_;
v___y_4662_ = v_a_4581_;
v___y_4663_ = v_a_4582_;
v___y_4664_ = v_a_4583_;
v___y_4665_ = v_a_4584_;
v___y_4666_ = v_a_4585_;
v___y_4667_ = v_a_4586_;
v___y_4668_ = v_a_4587_;
v___y_4669_ = v_a_4588_;
v___y_4670_ = v_a_4589_;
goto v___jp_4658_;
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4774_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4774_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
v___jp_4783_:
{
if (v___y_4784_ == 0)
{
lean_dec(v_a_4771_);
v___y_4659_ = v_a_4578_;
v___y_4660_ = v_a_4579_;
v___y_4661_ = v_a_4580_;
v___y_4662_ = v_a_4581_;
v___y_4663_ = v_a_4582_;
v___y_4664_ = v_a_4583_;
v___y_4665_ = v_a_4584_;
v___y_4666_ = v_a_4585_;
v___y_4667_ = v_a_4586_;
v___y_4668_ = v_a_4587_;
v___y_4669_ = v_a_4588_;
v___y_4670_ = v_a_4589_;
goto v___jp_4658_;
}
else
{
if (lean_obj_tag(v_a_4771_) == 0)
{
if (v___x_4705_ == 0)
{
v___y_4659_ = v_a_4578_;
v___y_4660_ = v_a_4579_;
v___y_4661_ = v_a_4580_;
v___y_4662_ = v_a_4581_;
v___y_4663_ = v_a_4582_;
v___y_4664_ = v_a_4583_;
v___y_4665_ = v_a_4584_;
v___y_4666_ = v_a_4585_;
v___y_4667_ = v_a_4586_;
v___y_4668_ = v_a_4587_;
v___y_4669_ = v_a_4588_;
v___y_4670_ = v_a_4589_;
goto v___jp_4658_;
}
else
{
goto v___jp_4772_;
}
}
else
{
lean_dec_ref_known(v_a_4771_, 1);
goto v___jp_4772_;
}
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec_ref(v_arg_4702_);
lean_dec_ref(v_arg_4657_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v_a_4792_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4770_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4770_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
else
{
lean_object* v___x_4800_; 
lean_dec_ref(v___x_4703_);
lean_dec_ref(v_arg_4702_);
lean_dec_ref(v_arg_4657_);
lean_inc_ref(v_arg_4624_);
v___x_4800_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_4624_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4874_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4803_ = v___x_4800_;
v_isShared_4804_ = v_isSharedCheck_4874_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4800_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4874_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
if (lean_obj_tag(v_a_4801_) == 1)
{
lean_object* v_val_4805_; lean_object* v___x_4806_; 
lean_del_object(v___x_4803_);
v_val_4805_ = lean_ctor_get(v_a_4801_, 0);
lean_inc(v_val_4805_);
lean_dec_ref_known(v_a_4801_, 1);
lean_inc_ref(v_arg_4621_);
v___x_4806_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_4621_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4869_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4869_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4869_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
if (lean_obj_tag(v_a_4807_) == 1)
{
lean_object* v_val_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4864_; 
lean_del_object(v___x_4809_);
v_val_4811_ = lean_ctor_get(v_a_4807_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v_a_4807_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4813_ = v_a_4807_;
v_isShared_4814_ = v_isSharedCheck_4864_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_val_4811_);
lean_dec(v_a_4807_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4864_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v_width_4815_; lean_object* v_bvExpr_4816_; lean_object* v_expr_4817_; lean_object* v_width_4818_; lean_object* v_bvExpr_4819_; lean_object* v_expr_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v_width_4815_ = lean_ctor_get(v_val_4805_, 0);
lean_inc_n(v_width_4815_, 2);
v_bvExpr_4816_ = lean_ctor_get(v_val_4805_, 1);
v_expr_4817_ = lean_ctor_get(v_val_4805_, 4);
lean_inc_ref(v_expr_4817_);
v_width_4818_ = lean_ctor_get(v_val_4811_, 0);
lean_inc_n(v_width_4818_, 2);
v_bvExpr_4819_ = lean_ctor_get(v_val_4811_, 1);
v_expr_4820_ = lean_ctor_get(v_val_4811_, 4);
lean_inc_ref(v_expr_4820_);
v___x_4821_ = lean_nat_add(v_width_4815_, v_width_4818_);
lean_inc_ref(v_bvExpr_4819_);
lean_inc_ref(v_bvExpr_4816_);
lean_inc_n(v___x_4821_, 2);
v___x_4822_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_width_4815_, v_width_4818_, v___x_4821_, v_bvExpr_4816_, v_bvExpr_4819_);
v___x_4823_ = l_Lean_mkNatLit(v___x_4821_);
lean_inc_ref(v___x_4823_);
v___x_4824_ = l_Lean_Meta_mkEqRefl(v___x_4823_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___f_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v___x_4826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_4827_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1));
v___x_4828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_4829_ = lean_box(0);
v___x_4830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75);
lean_inc(v_width_4815_);
v___x_4831_ = l_Lean_mkNatLit(v_width_4815_);
lean_inc(v_width_4818_);
v___x_4832_ = l_Lean_mkNatLit(v_width_4818_);
lean_inc_ref(v___x_4832_);
lean_inc_ref(v___x_4831_);
lean_inc_ref(v_expr_4820_);
lean_inc_ref(v_expr_4817_);
v___f_4833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed), 27, 15);
lean_closure_set(v___f_4833_, 0, v_width_4815_);
lean_closure_set(v___f_4833_, 1, v_expr_4817_);
lean_closure_set(v___f_4833_, 2, v_width_4818_);
lean_closure_set(v___f_4833_, 3, v_expr_4820_);
lean_closure_set(v___f_4833_, 4, v_val_4805_);
lean_closure_set(v___f_4833_, 5, v_val_4811_);
lean_closure_set(v___f_4833_, 6, v___x_4826_);
lean_closure_set(v___f_4833_, 7, v___x_4827_);
lean_closure_set(v___f_4833_, 8, v___x_4828_);
lean_closure_set(v___f_4833_, 9, v___x_4626_);
lean_closure_set(v___f_4833_, 10, v___x_4829_);
lean_closure_set(v___f_4833_, 11, v___x_4831_);
lean_closure_set(v___f_4833_, 12, v___x_4832_);
lean_closure_set(v___f_4833_, 13, v_arg_4624_);
lean_closure_set(v___f_4833_, 14, v_arg_4621_);
v___x_4834_ = l_Lean_mkApp6(v___x_4830_, v___x_4831_, v___x_4832_, v___x_4823_, v_expr_4817_, v_expr_4820_, v_a_4825_);
v___x_4835_ = l_Lean_Meta_Sym_shareCommonInc(v___x_4834_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4847_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4838_ = v___x_4835_;
v_isShared_4839_ = v_isSharedCheck_4847_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4835_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4847_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4840_; lean_object* v___x_4842_; 
v___x_4840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4821_);
lean_ctor_set(v___x_4840_, 1, v___x_4822_);
lean_ctor_set(v___x_4840_, 2, v_origExpr_4577_);
lean_ctor_set(v___x_4840_, 3, v___f_4833_);
lean_ctor_set(v___x_4840_, 4, v_a_4836_);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4840_);
v___x_4842_ = v___x_4813_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4840_);
v___x_4842_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_object* v___x_4844_; 
if (v_isShared_4839_ == 0)
{
lean_ctor_set(v___x_4838_, 0, v___x_4842_);
v___x_4844_ = v___x_4838_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_dec_ref(v___f_4833_);
lean_dec_ref(v___x_4822_);
lean_dec(v___x_4821_);
lean_del_object(v___x_4813_);
lean_dec_ref(v_origExpr_4577_);
v_a_4848_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4835_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4835_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec_ref(v___x_4823_);
lean_dec_ref(v___x_4822_);
lean_dec(v___x_4821_);
lean_dec_ref(v_expr_4820_);
lean_dec(v_width_4818_);
lean_dec_ref(v_expr_4817_);
lean_dec(v_width_4815_);
lean_del_object(v___x_4813_);
lean_dec(v_val_4811_);
lean_dec(v_val_4805_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v_a_4856_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4824_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4824_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
}
else
{
lean_object* v___x_4865_; lean_object* v___x_4867_; 
lean_dec(v_a_4807_);
lean_dec(v_val_4805_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4865_ = lean_box(0);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4865_);
v___x_4867_ = v___x_4809_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
else
{
lean_dec(v_val_4805_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
return v___x_4806_;
}
}
else
{
lean_object* v___x_4870_; lean_object* v___x_4872_; 
lean_dec(v_a_4801_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4870_ = lean_box(0);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v___x_4870_);
v___x_4872_ = v___x_4803_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4870_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
else
{
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
return v___x_4800_;
}
}
}
v___jp_4658_:
{
lean_object* v___x_4671_; uint8_t v___x_4672_; 
v___x_4671_ = l_Lean_Expr_cleanupAnnotations(v_arg_4657_);
v___x_4672_ = l_Lean_Expr_isApp(v___x_4671_);
if (v___x_4672_ == 0)
{
lean_dec_ref(v___x_4671_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4591_;
}
else
{
lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; 
v___x_4673_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4671_);
v___x_4674_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1));
v___x_4675_ = l_Lean_Expr_isConstOf(v___x_4673_, v___x_4674_);
lean_dec_ref(v___x_4673_);
if (v___x_4675_ == 0)
{
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4591_;
}
else
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25));
v___x_4677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27));
v___x_4678_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_4621_, v_arg_4624_, v___f_4608_, v___x_4676_, v___x_4677_, v_origExpr_4577_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
return v___x_4678_;
}
}
}
v___jp_4679_:
{
lean_object* v___x_4692_; uint8_t v___x_4693_; 
v___x_4692_ = l_Lean_Expr_cleanupAnnotations(v_arg_4657_);
v___x_4693_ = l_Lean_Expr_isApp(v___x_4692_);
if (v___x_4693_ == 0)
{
lean_dec_ref(v___x_4692_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4597_;
}
else
{
lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v___x_4694_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4692_);
v___x_4695_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_isValidBitVecAtom___redArg___closed__1));
v___x_4696_ = l_Lean_Expr_isConstOf(v___x_4694_, v___x_4695_);
lean_dec_ref(v___x_4694_);
if (v___x_4696_ == 0)
{
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
goto v___jp_4597_;
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29));
v___x_4698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31));
v___x_4699_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_4621_, v_arg_4624_, v___f_4607_, v___x_4697_, v___x_4698_, v_origExpr_4577_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
return v___x_4699_;
}
}
}
}
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
lean_dec_ref(v___x_4649_);
v___x_4875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77));
v___x_4876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79));
v___x_4877_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_4621_, v_arg_4624_, v___f_4609_, v___x_4875_, v___x_4876_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4877_;
}
}
else
{
lean_object* v___x_4878_; 
lean_dec_ref(v___x_4649_);
lean_inc_ref(v_arg_4636_);
v___x_4878_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_4636_);
if (lean_obj_tag(v___x_4878_) == 1)
{
lean_object* v_val_4879_; lean_object* v___x_4880_; 
v_val_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_val_4879_);
lean_dec_ref_known(v___x_4878_, 1);
lean_inc_ref(v_arg_4624_);
v___x_4880_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_4624_);
if (lean_obj_tag(v___x_4880_) == 1)
{
lean_object* v_val_4881_; lean_object* v___x_4882_; 
lean_del_object(v___x_4617_);
v_val_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_val_4881_);
lean_dec_ref_known(v___x_4880_, 1);
lean_inc_ref(v_arg_4621_);
v___x_4882_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_4621_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4929_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4885_ = v___x_4882_;
v_isShared_4886_ = v_isSharedCheck_4929_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4882_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4929_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
if (lean_obj_tag(v_a_4883_) == 1)
{
lean_object* v_val_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4924_; 
lean_del_object(v___x_4885_);
v_val_4887_ = lean_ctor_get(v_a_4883_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v_a_4883_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4889_ = v_a_4883_;
v_isShared_4890_ = v_isSharedCheck_4924_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_val_4887_);
lean_dec(v_a_4883_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4924_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v_width_4891_; lean_object* v_bvExpr_4892_; lean_object* v_expr_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___f_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v_width_4891_ = lean_ctor_get(v_val_4887_, 0);
lean_inc_n(v_width_4891_, 3);
v_bvExpr_4892_ = lean_ctor_get(v_val_4887_, 1);
v_expr_4893_ = lean_ctor_get(v_val_4887_, 4);
lean_inc_ref_n(v_expr_4893_, 2);
lean_inc_ref(v_bvExpr_4892_);
lean_inc(v_val_4881_);
v___x_4894_ = l_Std_Tactic_BVDecide_BVExpr_extract___override(v_width_4891_, v_val_4879_, v_val_4881_, v_bvExpr_4892_);
v___x_4895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_4896_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1));
v___x_4897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_4898_ = lean_box(0);
v___x_4899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82);
v___x_4900_ = l_Lean_mkNatLit(v_width_4891_);
lean_inc_ref(v___x_4900_);
lean_inc_ref(v_arg_4624_);
lean_inc_ref(v_arg_4636_);
v___f_4901_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___boxed), 24, 12);
lean_closure_set(v___f_4901_, 0, v_width_4891_);
lean_closure_set(v___f_4901_, 1, v_expr_4893_);
lean_closure_set(v___f_4901_, 2, v_val_4887_);
lean_closure_set(v___f_4901_, 3, v___x_4895_);
lean_closure_set(v___f_4901_, 4, v___x_4896_);
lean_closure_set(v___f_4901_, 5, v___x_4897_);
lean_closure_set(v___f_4901_, 6, v___x_4626_);
lean_closure_set(v___f_4901_, 7, v___x_4898_);
lean_closure_set(v___f_4901_, 8, v_arg_4636_);
lean_closure_set(v___f_4901_, 9, v_arg_4624_);
lean_closure_set(v___f_4901_, 10, v___x_4900_);
lean_closure_set(v___f_4901_, 11, v_arg_4621_);
v___x_4902_ = l_Lean_mkApp4(v___x_4899_, v___x_4900_, v_arg_4636_, v_arg_4624_, v_expr_4893_);
v___x_4903_ = l_Lean_Meta_Sym_shareCommonInc(v___x_4902_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4915_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4906_ = v___x_4903_;
v_isShared_4907_ = v_isSharedCheck_4915_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4903_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4915_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4908_; lean_object* v___x_4910_; 
v___x_4908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4908_, 0, v_val_4881_);
lean_ctor_set(v___x_4908_, 1, v___x_4894_);
lean_ctor_set(v___x_4908_, 2, v_origExpr_4577_);
lean_ctor_set(v___x_4908_, 3, v___f_4901_);
lean_ctor_set(v___x_4908_, 4, v_a_4904_);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4908_);
v___x_4910_ = v___x_4889_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4908_);
v___x_4910_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
lean_object* v___x_4912_; 
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 0, v___x_4910_);
v___x_4912_ = v___x_4906_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_dec_ref(v___f_4901_);
lean_dec_ref(v___x_4894_);
lean_del_object(v___x_4889_);
lean_dec(v_val_4881_);
lean_dec_ref(v_origExpr_4577_);
v_a_4916_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4903_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4903_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
else
{
lean_object* v___x_4925_; lean_object* v___x_4927_; 
lean_dec(v_a_4883_);
lean_dec(v_val_4881_);
lean_dec(v_val_4879_);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4925_ = lean_box(0);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 0, v___x_4925_);
v___x_4927_ = v___x_4885_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v___x_4925_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
else
{
lean_dec(v_val_4881_);
lean_dec(v_val_4879_);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
return v___x_4882_;
}
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4932_; 
lean_dec(v___x_4880_);
lean_dec(v_val_4879_);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4930_ = lean_box(0);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4930_);
v___x_4932_ = v___x_4617_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4930_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
else
{
lean_object* v___x_4934_; lean_object* v___x_4936_; 
lean_dec(v___x_4878_);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4934_ = lean_box(0);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4934_);
v___x_4936_ = v___x_4617_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
return v___x_4936_;
}
}
}
}
else
{
lean_object* v___x_4938_; 
lean_dec_ref(v___x_4649_);
lean_del_object(v___x_4617_);
lean_inc_ref(v_origExpr_4577_);
v___x_4938_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_origExpr_4577_, v___x_4651_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_5006_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4941_ = v___x_4938_;
v_isShared_4942_ = v_isSharedCheck_5006_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4938_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_5006_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
if (lean_obj_tag(v_a_4939_) == 1)
{
lean_object* v_val_4943_; lean_object* v___x_4944_; 
lean_del_object(v___x_4941_);
v_val_4943_ = lean_ctor_get(v_a_4939_, 0);
lean_inc_ref(v_arg_4636_);
v___x_4944_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v_arg_4636_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4993_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4947_ = v___x_4944_;
v_isShared_4948_ = v_isSharedCheck_4993_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4944_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4993_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
if (lean_obj_tag(v_a_4945_) == 1)
{
lean_object* v_val_4949_; lean_object* v___x_4950_; 
lean_del_object(v___x_4947_);
v_val_4949_ = lean_ctor_get(v_a_4945_, 0);
lean_inc(v_val_4949_);
lean_dec_ref_known(v_a_4945_, 1);
lean_inc_ref(v_arg_4624_);
v___x_4950_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_4624_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4988_; 
v_a_4951_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4953_ = v___x_4950_;
v_isShared_4954_ = v_isSharedCheck_4988_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4950_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4988_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
if (lean_obj_tag(v_a_4951_) == 1)
{
lean_object* v_val_4955_; lean_object* v___x_4956_; 
lean_del_object(v___x_4953_);
v_val_4955_ = lean_ctor_get(v_a_4951_, 0);
lean_inc(v_val_4955_);
lean_dec_ref_known(v_a_4951_, 1);
lean_inc_ref(v_arg_4621_);
v___x_4956_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_4621_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4983_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4959_ = v___x_4956_;
v_isShared_4960_ = v_isSharedCheck_4983_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4956_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4983_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
if (lean_obj_tag(v_a_4957_) == 1)
{
lean_object* v_val_4961_; lean_object* v___x_4962_; 
lean_del_object(v___x_4959_);
v_val_4961_ = lean_ctor_get(v_a_4957_, 0);
lean_inc(v_val_4961_);
lean_dec_ref_known(v_a_4957_, 1);
lean_inc(v_val_4943_);
v___x_4962_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(v_val_4949_, v_val_4943_, v_val_4955_, v_val_4961_, v_arg_4636_, v_origExpr_4577_, v_arg_4624_, v_arg_4621_, v_a_4578_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4969_; 
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4969_ == 0)
{
lean_object* v_unused_4970_; 
v_unused_4970_ = lean_ctor_get(v___x_4962_, 0);
lean_dec(v_unused_4970_);
v___x_4964_ = v___x_4962_;
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
else
{
lean_dec(v___x_4962_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4969_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4967_; 
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 0, v_a_4939_);
v___x_4967_ = v___x_4964_;
goto v_reusejp_4966_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4939_);
v___x_4967_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4966_;
}
v_reusejp_4966_:
{
return v___x_4967_;
}
}
}
else
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4978_; 
lean_dec_ref_known(v_a_4939_, 1);
v_a_4971_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4973_ = v___x_4962_;
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4962_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4971_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
else
{
lean_object* v___x_4979_; lean_object* v___x_4981_; 
lean_dec(v_a_4957_);
lean_dec(v_val_4955_);
lean_dec(v_val_4949_);
lean_dec_ref_known(v_a_4939_, 1);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4979_ = lean_box(0);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4979_);
v___x_4981_ = v___x_4959_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4979_);
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
else
{
lean_dec(v_val_4955_);
lean_dec(v_val_4949_);
lean_dec_ref_known(v_a_4939_, 1);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
return v___x_4956_;
}
}
else
{
lean_object* v___x_4984_; lean_object* v___x_4986_; 
lean_dec(v_a_4951_);
lean_dec(v_val_4949_);
lean_dec_ref_known(v_a_4939_, 1);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4984_ = lean_box(0);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 0, v___x_4984_);
v___x_4986_ = v___x_4953_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4984_);
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
else
{
lean_dec(v_val_4949_);
lean_dec_ref_known(v_a_4939_, 1);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
return v___x_4950_;
}
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4991_; 
lean_dec(v_a_4945_);
lean_dec_ref_known(v_a_4939_, 1);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_4989_ = lean_box(0);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 0, v___x_4989_);
v___x_4991_ = v___x_4947_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
lean_dec_ref_known(v_a_4939_, 1);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v_a_4994_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4944_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4944_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4999_; 
if (v_isShared_4997_ == 0)
{
v___x_4999_ = v___x_4996_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4994_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
else
{
lean_object* v___x_5002_; lean_object* v___x_5004_; 
lean_dec(v_a_4939_);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_5002_ = lean_box(0);
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 0, v___x_5002_);
v___x_5004_ = v___x_4941_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_5002_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
else
{
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
return v___x_4938_;
}
}
}
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
lean_dec_ref(v___x_4637_);
lean_dec_ref(v_arg_4636_);
lean_dec_ref(v_arg_4624_);
lean_del_object(v___x_4617_);
v___x_5007_ = lean_box(0);
v___x_5008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84));
v___x_5009_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_4621_, v___x_5007_, v___x_5008_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5009_;
}
}
else
{
lean_object* v___x_5010_; 
lean_dec_ref(v___x_4637_);
lean_dec_ref(v_arg_4636_);
v___x_5010_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_4621_);
if (lean_obj_tag(v___x_5010_) == 1)
{
lean_object* v_val_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
lean_del_object(v___x_4617_);
v_val_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_val_5011_);
lean_dec_ref_known(v___x_5010_, 1);
v___x_5012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_5013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86));
v___x_5014_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_5011_, v_arg_4624_, v___f_4606_, v___x_5012_, v___x_5013_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5014_;
}
else
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
lean_dec(v___x_5010_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_origExpr_4577_);
v___x_5015_ = lean_box(0);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_5015_);
v___x_5017_ = v___x_4617_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
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
else
{
lean_object* v___x_5019_; 
lean_dec_ref(v___x_4637_);
lean_dec_ref(v_arg_4636_);
lean_del_object(v___x_4617_);
lean_inc_ref(v_arg_4621_);
v___x_5019_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_4621_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5085_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5085_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5085_ == 0)
{
v___x_5022_ = v___x_5019_;
v_isShared_5023_ = v_isSharedCheck_5085_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5019_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5085_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
if (lean_obj_tag(v_a_5020_) == 1)
{
lean_object* v_val_5024_; lean_object* v___x_5025_; 
v_val_5024_ = lean_ctor_get(v_a_5020_, 0);
lean_inc(v_val_5024_);
lean_dec_ref_known(v_a_5020_, 1);
v___x_5025_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_4624_);
if (lean_obj_tag(v___x_5025_) == 1)
{
lean_object* v_val_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5076_; 
lean_del_object(v___x_5022_);
v_val_5026_ = lean_ctor_get(v___x_5025_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5025_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5028_ = v___x_5025_;
v_isShared_5029_ = v_isSharedCheck_5076_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_val_5026_);
lean_dec(v___x_5025_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5076_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v_width_5030_; lean_object* v_bvExpr_5031_; lean_object* v_expr_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v_width_5030_ = lean_ctor_get(v_val_5024_, 0);
lean_inc_n(v_width_5030_, 2);
v_bvExpr_5031_ = lean_ctor_get(v_val_5024_, 1);
v_expr_5032_ = lean_ctor_get(v_val_5024_, 4);
lean_inc_ref(v_expr_5032_);
v___x_5033_ = lean_nat_mul(v_width_5030_, v_val_5026_);
lean_inc_ref(v_bvExpr_5031_);
lean_inc(v_val_5026_);
lean_inc_n(v___x_5033_, 2);
v___x_5034_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_width_5030_, v___x_5033_, v_val_5026_, v_bvExpr_5031_);
v___x_5035_ = l_Lean_mkNatLit(v___x_5033_);
lean_inc_ref(v___x_5035_);
v___x_5036_ = l_Lean_Meta_mkEqRefl(v___x_5035_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___f_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_5039_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_checkFunAtom_spec__6___closed__1));
v___x_5040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_5041_ = lean_box(0);
v___x_5042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88);
lean_inc(v_width_5030_);
v___x_5043_ = l_Lean_mkNatLit(v_width_5030_);
v___x_5044_ = l_Lean_mkNatLit(v_val_5026_);
lean_inc_ref(v___x_5043_);
lean_inc_ref(v___x_5044_);
lean_inc_ref(v_expr_5032_);
v___f_5045_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___boxed), 23, 11);
lean_closure_set(v___f_5045_, 0, v_width_5030_);
lean_closure_set(v___f_5045_, 1, v_expr_5032_);
lean_closure_set(v___f_5045_, 2, v_val_5024_);
lean_closure_set(v___f_5045_, 3, v___x_5038_);
lean_closure_set(v___f_5045_, 4, v___x_5039_);
lean_closure_set(v___f_5045_, 5, v___x_5040_);
lean_closure_set(v___f_5045_, 6, v___x_4626_);
lean_closure_set(v___f_5045_, 7, v___x_5041_);
lean_closure_set(v___f_5045_, 8, v___x_5044_);
lean_closure_set(v___f_5045_, 9, v___x_5043_);
lean_closure_set(v___f_5045_, 10, v_arg_4621_);
v___x_5046_ = l_Lean_mkApp5(v___x_5042_, v___x_5043_, v___x_5035_, v___x_5044_, v_expr_5032_, v_a_5037_);
v___x_5047_ = l_Lean_Meta_Sym_shareCommonInc(v___x_5046_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5059_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5050_ = v___x_5047_;
v_isShared_5051_ = v_isSharedCheck_5059_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5047_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5059_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5052_; lean_object* v___x_5054_; 
v___x_5052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5033_);
lean_ctor_set(v___x_5052_, 1, v___x_5034_);
lean_ctor_set(v___x_5052_, 2, v_origExpr_4577_);
lean_ctor_set(v___x_5052_, 3, v___f_5045_);
lean_ctor_set(v___x_5052_, 4, v_a_5048_);
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 0, v___x_5052_);
v___x_5054_ = v___x_5028_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5052_);
v___x_5054_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
lean_object* v___x_5056_; 
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v___x_5054_);
v___x_5056_ = v___x_5050_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5054_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
lean_dec_ref(v___f_5045_);
lean_dec_ref(v___x_5034_);
lean_dec(v___x_5033_);
lean_del_object(v___x_5028_);
lean_dec_ref(v_origExpr_4577_);
v_a_5060_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_5047_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5047_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec_ref(v___x_5035_);
lean_dec_ref(v___x_5034_);
lean_dec(v___x_5033_);
lean_dec_ref(v_expr_5032_);
lean_dec(v_width_5030_);
lean_del_object(v___x_5028_);
lean_dec(v_val_5026_);
lean_dec(v_val_5024_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v_a_5068_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5036_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5036_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
else
{
lean_object* v___x_5077_; lean_object* v___x_5079_; 
lean_dec(v___x_5025_);
lean_dec(v_val_5024_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_5077_ = lean_box(0);
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v___x_5077_);
v___x_5079_ = v___x_5022_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5077_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
return v___x_5079_;
}
}
}
else
{
lean_object* v___x_5081_; lean_object* v___x_5083_; 
lean_dec(v_a_5020_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
v___x_5081_ = lean_box(0);
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v___x_5081_);
v___x_5083_ = v___x_5022_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
return v___x_5083_;
}
}
}
}
else
{
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_dec_ref(v_origExpr_4577_);
return v___x_5019_;
}
}
}
else
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; 
lean_dec_ref(v___x_4637_);
lean_dec_ref(v_arg_4636_);
lean_del_object(v___x_4617_);
v___x_5086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_5087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90));
v___x_5088_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_4621_, v_arg_4624_, v___f_4610_, v___x_5086_, v___x_5087_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5088_;
}
}
else
{
lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
lean_dec_ref(v___x_4637_);
lean_dec_ref(v_arg_4636_);
lean_del_object(v___x_4617_);
v___x_5089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_5090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92));
v___x_5091_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_4621_, v_arg_4624_, v___f_4611_, v___x_5089_, v___x_5090_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5091_;
}
}
}
else
{
lean_object* v___x_5092_; 
lean_dec_ref(v___x_4625_);
lean_dec_ref(v_arg_4624_);
lean_dec_ref(v_arg_4621_);
lean_del_object(v___x_4617_);
v___x_5092_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5092_;
}
}
else
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
lean_dec_ref(v___x_4625_);
lean_dec_ref(v_arg_4624_);
lean_del_object(v___x_4617_);
v___x_5093_ = lean_box(4);
v___x_5094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94));
v___x_5095_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_4621_, v___x_5093_, v___x_5094_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5095_;
}
}
else
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
lean_dec_ref(v___x_4625_);
lean_dec_ref(v_arg_4624_);
lean_del_object(v___x_4617_);
v___x_5096_ = lean_box(5);
v___x_5097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96));
v___x_5098_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_4621_, v___x_5096_, v___x_5097_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5098_;
}
}
else
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
lean_dec_ref(v___x_4625_);
lean_dec_ref(v_arg_4624_);
lean_del_object(v___x_4617_);
v___x_5099_ = lean_box(6);
v___x_5100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98));
v___x_5101_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_4621_, v___x_5099_, v___x_5100_, v_origExpr_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_5101_;
}
}
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v_origExpr_4577_);
v_a_5103_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_4614_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_4614_);
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
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec_ref(v_origExpr_4577_);
v_a_5111_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_4613_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_4613_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
v___jp_4591_:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = lean_box(0);
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
v___jp_4594_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_box(0);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
v___jp_4597_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = lean_box(0);
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
return v___x_4599_;
}
v___jp_4600_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4601_ = lean_box(0);
v___x_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
return v___x_4602_;
}
v___jp_4603_:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_box(0);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
return v___x_4605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object* v_e_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v___y_5134_; lean_object* v___x_5157_; lean_object* v_bvExprCache_5158_; lean_object* v___x_5159_; 
v___x_5157_ = lean_st_ref_get(v_a_5120_);
v_bvExprCache_5158_ = lean_ctor_get(v___x_5157_, 1);
lean_inc_ref(v_bvExprCache_5158_);
lean_dec(v___x_5157_);
v___x_5159_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg(v_bvExprCache_5158_, v_e_5119_);
lean_dec_ref(v_bvExprCache_5158_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v___x_5160_; 
lean_inc_ref(v_e_5119_);
v___x_5160_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_e_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_object* v_a_5161_; 
v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
if (lean_obj_tag(v_a_5161_) == 0)
{
uint8_t v___x_5162_; lean_object* v___x_5163_; 
lean_dec_ref_known(v___x_5160_, 1);
v___x_5162_ = 0;
lean_inc_ref(v_e_5119_);
v___x_5163_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_e_5119_, v___x_5162_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
v___y_5134_ = v___x_5163_;
goto v___jp_5133_;
}
else
{
v___y_5134_ = v___x_5160_;
goto v___jp_5133_;
}
}
else
{
v___y_5134_ = v___x_5160_;
goto v___jp_5133_;
}
}
else
{
lean_object* v_val_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec_ref(v_e_5119_);
v_val_5164_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5159_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_val_5164_);
lean_dec(v___x_5159_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
lean_ctor_set_tag(v___x_5166_, 0);
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_val_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
v___jp_5133_:
{
if (lean_obj_tag(v___y_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5156_; 
v_a_5135_ = lean_ctor_get(v___y_5134_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___y_5134_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5137_ = v___y_5134_;
v_isShared_5138_ = v_isSharedCheck_5156_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___y_5134_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5156_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5139_; lean_object* v_lemmas_5140_; lean_object* v_bvExprCache_5141_; lean_object* v_bvPredCache_5142_; lean_object* v_bvLogicalCache_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5155_; 
v___x_5139_ = lean_st_ref_take(v_a_5120_);
v_lemmas_5140_ = lean_ctor_get(v___x_5139_, 0);
v_bvExprCache_5141_ = lean_ctor_get(v___x_5139_, 1);
v_bvPredCache_5142_ = lean_ctor_get(v___x_5139_, 2);
v_bvLogicalCache_5143_ = lean_ctor_get(v___x_5139_, 3);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5145_ = v___x_5139_;
v_isShared_5146_ = v_isSharedCheck_5155_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_bvLogicalCache_5143_);
lean_inc(v_bvPredCache_5142_);
lean_inc(v_bvExprCache_5141_);
lean_inc(v_lemmas_5140_);
lean_dec(v___x_5139_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5155_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5147_; lean_object* v___x_5149_; 
lean_inc(v_a_5135_);
v___x_5147_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17___redArg(v_bvExprCache_5141_, v_e_5119_, v_a_5135_);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 1, v___x_5147_);
v___x_5149_ = v___x_5145_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_lemmas_5140_);
lean_ctor_set(v_reuseFailAlloc_5154_, 1, v___x_5147_);
lean_ctor_set(v_reuseFailAlloc_5154_, 2, v_bvPredCache_5142_);
lean_ctor_set(v_reuseFailAlloc_5154_, 3, v_bvLogicalCache_5143_);
v___x_5149_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
lean_object* v___x_5150_; lean_object* v___x_5152_; 
v___x_5150_ = lean_st_ref_put(v_a_5120_, v___x_5149_);
if (v_isShared_5138_ == 0)
{
v___x_5152_ = v___x_5137_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5135_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_5119_);
return v___y_5134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(lean_object* v_origExpr_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_origExpr_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(lean_object* v_origExpr_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v___x_5201_; 
v___x_5201_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of___boxed(lean_object* v_origExpr_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_origExpr_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_);
lean_dec(v_a_5214_);
lean_dec_ref(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_a_5211_);
lean_dec(v_a_5210_);
lean_dec_ref(v_a_5209_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5207_);
lean_dec(v_a_5206_);
lean_dec(v_a_5205_);
lean_dec_ref(v_a_5204_);
lean_dec(v_a_5203_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of___boxed(lean_object* v_origExpr_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v_origExpr_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_);
lean_dec(v_a_5229_);
lean_dec_ref(v_a_5228_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
lean_dec(v_a_5220_);
lean_dec_ref(v_a_5219_);
lean_dec(v_a_5218_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of___boxed(lean_object* v_origExpr_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(v_origExpr_5232_, v_a_5233_, v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_, v_a_5243_, v_a_5244_);
lean_dec(v_a_5244_);
lean_dec_ref(v_a_5243_);
lean_dec(v_a_5242_);
lean_dec_ref(v_a_5241_);
lean_dec(v_a_5240_);
lean_dec_ref(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_a_5237_);
lean_dec(v_a_5236_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
lean_dec(v_a_5233_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom___boxed(lean_object* v_origExpr_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec(v_a_5251_);
lean_dec(v_a_5250_);
lean_dec_ref(v_a_5249_);
lean_dec(v_a_5248_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom___boxed(lean_object* v_origExpr_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
lean_dec(v_a_5274_);
lean_dec_ref(v_a_5273_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
lean_dec(v_a_5270_);
lean_dec_ref(v_a_5269_);
lean_dec(v_a_5268_);
lean_dec_ref(v_a_5267_);
lean_dec(v_a_5266_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec(v_a_5263_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection___boxed(lean_object** _args){
lean_object* v_distanceExpr_5277_ = _args[0];
lean_object* v_innerExpr_5278_ = _args[1];
lean_object* v_rotateOp_5279_ = _args[2];
lean_object* v_rotateOpName_5280_ = _args[3];
lean_object* v_congrThm_5281_ = _args[4];
lean_object* v_origExpr_5282_ = _args[5];
lean_object* v_a_5283_ = _args[6];
lean_object* v_a_5284_ = _args[7];
lean_object* v_a_5285_ = _args[8];
lean_object* v_a_5286_ = _args[9];
lean_object* v_a_5287_ = _args[10];
lean_object* v_a_5288_ = _args[11];
lean_object* v_a_5289_ = _args[12];
lean_object* v_a_5290_ = _args[13];
lean_object* v_a_5291_ = _args[14];
lean_object* v_a_5292_ = _args[15];
lean_object* v_a_5293_ = _args[16];
lean_object* v_a_5294_ = _args[17];
lean_object* v_a_5295_ = _args[18];
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_distanceExpr_5277_, v_innerExpr_5278_, v_rotateOp_5279_, v_rotateOpName_5280_, v_congrThm_5281_, v_origExpr_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_);
lean_dec(v_a_5294_);
lean_dec_ref(v_a_5293_);
lean_dec(v_a_5292_);
lean_dec_ref(v_a_5291_);
lean_dec(v_a_5290_);
lean_dec_ref(v_a_5289_);
lean_dec(v_a_5288_);
lean_dec_ref(v_a_5287_);
lean_dec(v_a_5286_);
lean_dec(v_a_5285_);
lean_dec_ref(v_a_5284_);
lean_dec(v_a_5283_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit___boxed(lean_object* v_x_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_x_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
lean_dec(v_a_5309_);
lean_dec_ref(v_a_5308_);
lean_dec(v_a_5307_);
lean_dec_ref(v_a_5306_);
lean_dec(v_a_5305_);
lean_dec_ref(v_a_5304_);
lean_dec(v_a_5303_);
lean_dec_ref(v_a_5302_);
lean_dec(v_a_5301_);
lean_dec(v_a_5300_);
lean_dec_ref(v_a_5299_);
lean_dec(v_a_5298_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom___boxed(lean_object* v_e_5312_, lean_object* v_synthetic_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_){
_start:
{
uint8_t v_synthetic_boxed_5327_; lean_object* v_res_5328_; 
v_synthetic_boxed_5327_ = lean_unbox(v_synthetic_5313_);
v_res_5328_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_e_5312_, v_synthetic_boxed_5327_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_);
lean_dec(v_a_5325_);
lean_dec_ref(v_a_5324_);
lean_dec(v_a_5323_);
lean_dec_ref(v_a_5322_);
lean_dec(v_a_5321_);
lean_dec_ref(v_a_5320_);
lean_dec(v_a_5319_);
lean_dec_ref(v_a_5318_);
lean_dec(v_a_5317_);
lean_dec(v_a_5316_);
lean_dec_ref(v_a_5315_);
lean_dec(v_a_5314_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom___boxed(lean_object* v_t_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(v_t_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_);
lean_dec(v_a_5341_);
lean_dec_ref(v_a_5340_);
lean_dec(v_a_5339_);
lean_dec_ref(v_a_5338_);
lean_dec(v_a_5337_);
lean_dec_ref(v_a_5336_);
lean_dec(v_a_5335_);
lean_dec_ref(v_a_5334_);
lean_dec(v_a_5333_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred___boxed(lean_object* v_origExpr_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_);
lean_dec(v_a_5356_);
lean_dec_ref(v_a_5355_);
lean_dec(v_a_5354_);
lean_dec_ref(v_a_5353_);
lean_dec(v_a_5352_);
lean_dec_ref(v_a_5351_);
lean_dec(v_a_5350_);
lean_dec_ref(v_a_5349_);
lean_dec(v_a_5348_);
lean_dec(v_a_5347_);
lean_dec_ref(v_a_5346_);
lean_dec(v_a_5345_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection___boxed(lean_object** _args){
lean_object* v_lhsExpr_5359_ = _args[0];
lean_object* v_rhsExpr_5360_ = _args[1];
lean_object* v_pred_5361_ = _args[2];
lean_object* v_origExpr_5362_ = _args[3];
lean_object* v_a_5363_ = _args[4];
lean_object* v_a_5364_ = _args[5];
lean_object* v_a_5365_ = _args[6];
lean_object* v_a_5366_ = _args[7];
lean_object* v_a_5367_ = _args[8];
lean_object* v_a_5368_ = _args[9];
lean_object* v_a_5369_ = _args[10];
lean_object* v_a_5370_ = _args[11];
lean_object* v_a_5371_ = _args[12];
lean_object* v_a_5372_ = _args[13];
lean_object* v_a_5373_ = _args[14];
lean_object* v_a_5374_ = _args[15];
lean_object* v_a_5375_ = _args[16];
_start:
{
uint8_t v_pred_boxed_5376_; lean_object* v_res_5377_; 
v_pred_boxed_5376_ = lean_unbox(v_pred_5361_);
v_res_5377_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_lhsExpr_5359_, v_rhsExpr_5360_, v_pred_boxed_5376_, v_origExpr_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_);
lean_dec(v_a_5374_);
lean_dec_ref(v_a_5373_);
lean_dec(v_a_5372_);
lean_dec_ref(v_a_5371_);
lean_dec(v_a_5370_);
lean_dec_ref(v_a_5369_);
lean_dec(v_a_5368_);
lean_dec_ref(v_a_5367_);
lean_dec(v_a_5366_);
lean_dec(v_a_5365_);
lean_dec_ref(v_a_5364_);
lean_dec(v_a_5363_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection___boxed(lean_object** _args){
lean_object* v_lhsExpr_5378_ = _args[0];
lean_object* v_rhsExpr_5379_ = _args[1];
lean_object* v_gate_5380_ = _args[2];
lean_object* v_origExpr_5381_ = _args[3];
lean_object* v_a_5382_ = _args[4];
lean_object* v_a_5383_ = _args[5];
lean_object* v_a_5384_ = _args[6];
lean_object* v_a_5385_ = _args[7];
lean_object* v_a_5386_ = _args[8];
lean_object* v_a_5387_ = _args[9];
lean_object* v_a_5388_ = _args[10];
lean_object* v_a_5389_ = _args[11];
lean_object* v_a_5390_ = _args[12];
lean_object* v_a_5391_ = _args[13];
lean_object* v_a_5392_ = _args[14];
lean_object* v_a_5393_ = _args[15];
lean_object* v_a_5394_ = _args[16];
_start:
{
uint8_t v_gate_boxed_5395_; lean_object* v_res_5396_; 
v_gate_boxed_5395_ = lean_unbox(v_gate_5380_);
v_res_5396_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_lhsExpr_5378_, v_rhsExpr_5379_, v_gate_boxed_5395_, v_origExpr_5381_, v_a_5382_, v_a_5383_, v_a_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_);
lean_dec(v_a_5393_);
lean_dec_ref(v_a_5392_);
lean_dec(v_a_5391_);
lean_dec_ref(v_a_5390_);
lean_dec(v_a_5389_);
lean_dec_ref(v_a_5388_);
lean_dec(v_a_5387_);
lean_dec_ref(v_a_5386_);
lean_dec(v_a_5385_);
lean_dec(v_a_5384_);
lean_dec_ref(v_a_5383_);
lean_dec(v_a_5382_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object* v_e_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_e_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
lean_dec(v_a_5409_);
lean_dec_ref(v_a_5408_);
lean_dec(v_a_5407_);
lean_dec_ref(v_a_5406_);
lean_dec(v_a_5405_);
lean_dec_ref(v_a_5404_);
lean_dec(v_a_5403_);
lean_dec_ref(v_a_5402_);
lean_dec(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
lean_dec(v_a_5398_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__23___boxed(lean_object* v_e_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_){
_start:
{
lean_object* v_res_5426_; 
v_res_5426_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__23(v_e_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_);
lean_dec(v_a_5424_);
lean_dec_ref(v_a_5423_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec(v_a_5420_);
lean_dec_ref(v_a_5419_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec(v_a_5416_);
lean_dec(v_a_5415_);
lean_dec_ref(v_a_5414_);
lean_dec(v_a_5413_);
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object* v_e_5427_, lean_object* v_a_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_e_5427_, v_a_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_);
lean_dec(v_a_5439_);
lean_dec_ref(v_a_5438_);
lean_dec(v_a_5437_);
lean_dec_ref(v_a_5436_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
lean_dec(v_a_5433_);
lean_dec_ref(v_a_5432_);
lean_dec(v_a_5431_);
lean_dec(v_a_5430_);
lean_dec_ref(v_a_5429_);
lean_dec(v_a_5428_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object** _args){
lean_object* v_distance_5442_ = _args[0];
lean_object* v_innerExpr_5443_ = _args[1];
lean_object* v_shiftOp_5444_ = _args[2];
lean_object* v_shiftOpName_5445_ = _args[3];
lean_object* v_congrThm_5446_ = _args[4];
lean_object* v_origExpr_5447_ = _args[5];
lean_object* v_a_5448_ = _args[6];
lean_object* v_a_5449_ = _args[7];
lean_object* v_a_5450_ = _args[8];
lean_object* v_a_5451_ = _args[9];
lean_object* v_a_5452_ = _args[10];
lean_object* v_a_5453_ = _args[11];
lean_object* v_a_5454_ = _args[12];
lean_object* v_a_5455_ = _args[13];
lean_object* v_a_5456_ = _args[14];
lean_object* v_a_5457_ = _args[15];
lean_object* v_a_5458_ = _args[16];
lean_object* v_a_5459_ = _args[17];
lean_object* v_a_5460_ = _args[18];
_start:
{
lean_object* v_res_5461_; 
v_res_5461_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_distance_5442_, v_innerExpr_5443_, v_shiftOp_5444_, v_shiftOpName_5445_, v_congrThm_5446_, v_origExpr_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_, v_a_5457_, v_a_5458_, v_a_5459_);
lean_dec(v_a_5459_);
lean_dec_ref(v_a_5458_);
lean_dec(v_a_5457_);
lean_dec_ref(v_a_5456_);
lean_dec(v_a_5455_);
lean_dec_ref(v_a_5454_);
lean_dec(v_a_5453_);
lean_dec_ref(v_a_5452_);
lean_dec(v_a_5451_);
lean_dec(v_a_5450_);
lean_dec_ref(v_a_5449_);
lean_dec(v_a_5448_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection___boxed(lean_object** _args){
lean_object* v_distanceExpr_5462_ = _args[0];
lean_object* v_innerExpr_5463_ = _args[1];
lean_object* v_shiftOp_5464_ = _args[2];
lean_object* v_shiftOpName_5465_ = _args[3];
lean_object* v_congrThm_5466_ = _args[4];
lean_object* v_origExpr_5467_ = _args[5];
lean_object* v_a_5468_ = _args[6];
lean_object* v_a_5469_ = _args[7];
lean_object* v_a_5470_ = _args[8];
lean_object* v_a_5471_ = _args[9];
lean_object* v_a_5472_ = _args[10];
lean_object* v_a_5473_ = _args[11];
lean_object* v_a_5474_ = _args[12];
lean_object* v_a_5475_ = _args[13];
lean_object* v_a_5476_ = _args[14];
lean_object* v_a_5477_ = _args[15];
lean_object* v_a_5478_ = _args[16];
lean_object* v_a_5479_ = _args[17];
lean_object* v_a_5480_ = _args[18];
_start:
{
lean_object* v_res_5481_; 
v_res_5481_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_distanceExpr_5462_, v_innerExpr_5463_, v_shiftOp_5464_, v_shiftOpName_5465_, v_congrThm_5466_, v_origExpr_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_);
lean_dec(v_a_5479_);
lean_dec_ref(v_a_5478_);
lean_dec(v_a_5477_);
lean_dec_ref(v_a_5476_);
lean_dec(v_a_5475_);
lean_dec_ref(v_a_5474_);
lean_dec(v_a_5473_);
lean_dec_ref(v_a_5472_);
lean_dec(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___boxed(lean_object* v_e_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_, lean_object* v_a_5488_, lean_object* v_a_5489_, lean_object* v_a_5490_, lean_object* v_a_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_){
_start:
{
lean_object* v_res_5496_; 
v_res_5496_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(v_e_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_, v_a_5488_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_, v_a_5493_, v_a_5494_);
lean_dec(v_a_5494_);
lean_dec_ref(v_a_5493_);
lean_dec(v_a_5492_);
lean_dec_ref(v_a_5491_);
lean_dec(v_a_5490_);
lean_dec_ref(v_a_5489_);
lean_dec(v_a_5488_);
lean_dec_ref(v_a_5487_);
lean_dec(v_a_5486_);
lean_dec(v_a_5485_);
lean_dec_ref(v_a_5484_);
lean_dec(v_a_5483_);
return v_res_5496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom___boxed(lean_object* v_e_5497_, lean_object* v_width_5498_, lean_object* v_synthetic_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_, lean_object* v_a_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_){
_start:
{
uint8_t v_synthetic_boxed_5513_; lean_object* v_res_5514_; 
v_synthetic_boxed_5513_ = lean_unbox(v_synthetic_5499_);
v_res_5514_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom(v_e_5497_, v_width_5498_, v_synthetic_boxed_5513_, v_a_5500_, v_a_5501_, v_a_5502_, v_a_5503_, v_a_5504_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
lean_dec(v_a_5511_);
lean_dec_ref(v_a_5510_);
lean_dec(v_a_5509_);
lean_dec_ref(v_a_5508_);
lean_dec(v_a_5507_);
lean_dec_ref(v_a_5506_);
lean_dec(v_a_5505_);
lean_dec_ref(v_a_5504_);
lean_dec(v_a_5503_);
lean_dec(v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec(v_a_5500_);
return v_res_5514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_spec__6___boxed(lean_object** _args){
lean_object* v_as_5515_ = _args[0];
lean_object* v_i_5516_ = _args[1];
lean_object* v_stop_5517_ = _args[2];
lean_object* v_b_5518_ = _args[3];
lean_object* v___y_5519_ = _args[4];
lean_object* v___y_5520_ = _args[5];
lean_object* v___y_5521_ = _args[6];
lean_object* v___y_5522_ = _args[7];
lean_object* v___y_5523_ = _args[8];
lean_object* v___y_5524_ = _args[9];
lean_object* v___y_5525_ = _args[10];
lean_object* v___y_5526_ = _args[11];
lean_object* v___y_5527_ = _args[12];
lean_object* v___y_5528_ = _args[13];
lean_object* v___y_5529_ = _args[14];
lean_object* v___y_5530_ = _args[15];
lean_object* v___y_5531_ = _args[16];
_start:
{
size_t v_i_boxed_5532_; size_t v_stop_boxed_5533_; lean_object* v_res_5534_; 
v_i_boxed_5532_ = lean_unbox_usize(v_i_5516_);
lean_dec(v_i_5516_);
v_stop_boxed_5533_ = lean_unbox_usize(v_stop_5517_);
lean_dec(v_stop_5517_);
v_res_5534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_registerAtom_spec__6(v_as_5515_, v_i_boxed_5532_, v_stop_boxed_5533_, v_b_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
lean_dec(v___y_5528_);
lean_dec_ref(v___y_5527_);
lean_dec(v___y_5526_);
lean_dec_ref(v___y_5525_);
lean_dec(v___y_5524_);
lean_dec_ref(v___y_5523_);
lean_dec(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v_as_5515_);
return v_res_5534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___boxed(lean_object** _args){
lean_object* v_innerExpr_5535_ = _args[0];
lean_object* v_op_5536_ = _args[1];
lean_object* v_congrThm_5537_ = _args[2];
lean_object* v_origExpr_5538_ = _args[3];
lean_object* v_a_5539_ = _args[4];
lean_object* v_a_5540_ = _args[5];
lean_object* v_a_5541_ = _args[6];
lean_object* v_a_5542_ = _args[7];
lean_object* v_a_5543_ = _args[8];
lean_object* v_a_5544_ = _args[9];
lean_object* v_a_5545_ = _args[10];
lean_object* v_a_5546_ = _args[11];
lean_object* v_a_5547_ = _args[12];
lean_object* v_a_5548_ = _args[13];
lean_object* v_a_5549_ = _args[14];
lean_object* v_a_5550_ = _args[15];
lean_object* v_a_5551_ = _args[16];
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_innerExpr_5535_, v_op_5536_, v_congrThm_5537_, v_origExpr_5538_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
lean_dec(v_a_5550_);
lean_dec_ref(v_a_5549_);
lean_dec(v_a_5548_);
lean_dec_ref(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
lean_dec(v_a_5544_);
lean_dec_ref(v_a_5543_);
lean_dec(v_a_5542_);
lean_dec(v_a_5541_);
lean_dec_ref(v_a_5540_);
lean_dec(v_a_5539_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___boxed(lean_object** _args){
lean_object* v_lhsExpr_5553_ = _args[0];
lean_object* v_rhsExpr_5554_ = _args[1];
lean_object* v_op_5555_ = _args[2];
lean_object* v_congrThm_5556_ = _args[3];
lean_object* v_origExpr_5557_ = _args[4];
lean_object* v_a_5558_ = _args[5];
lean_object* v_a_5559_ = _args[6];
lean_object* v_a_5560_ = _args[7];
lean_object* v_a_5561_ = _args[8];
lean_object* v_a_5562_ = _args[9];
lean_object* v_a_5563_ = _args[10];
lean_object* v_a_5564_ = _args[11];
lean_object* v_a_5565_ = _args[12];
lean_object* v_a_5566_ = _args[13];
lean_object* v_a_5567_ = _args[14];
lean_object* v_a_5568_ = _args[15];
lean_object* v_a_5569_ = _args[16];
lean_object* v_a_5570_ = _args[17];
_start:
{
uint8_t v_op_boxed_5571_; lean_object* v_res_5572_; 
v_op_boxed_5571_ = lean_unbox(v_op_5555_);
v_res_5572_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_lhsExpr_5553_, v_rhsExpr_5554_, v_op_boxed_5571_, v_congrThm_5556_, v_origExpr_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
lean_dec(v_a_5569_);
lean_dec_ref(v_a_5568_);
lean_dec(v_a_5567_);
lean_dec_ref(v_a_5566_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v_a_5559_);
lean_dec(v_a_5558_);
return v_res_5572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___boxed(lean_object* v_origExpr_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_){
_start:
{
lean_object* v_res_5587_; 
v_res_5587_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_origExpr_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_);
lean_dec(v_a_5585_);
lean_dec_ref(v_a_5584_);
lean_dec(v_a_5583_);
lean_dec_ref(v_a_5582_);
lean_dec(v_a_5581_);
lean_dec_ref(v_a_5580_);
lean_dec(v_a_5579_);
lean_dec_ref(v_a_5578_);
lean_dec(v_a_5577_);
lean_dec(v_a_5576_);
lean_dec_ref(v_a_5575_);
lean_dec(v_a_5574_);
return v_res_5587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___boxed(lean_object* v_origExpr_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_){
_start:
{
lean_object* v_res_5602_; 
v_res_5602_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_origExpr_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_, v_a_5600_);
lean_dec(v_a_5600_);
lean_dec_ref(v_a_5599_);
lean_dec(v_a_5598_);
lean_dec_ref(v_a_5597_);
lean_dec(v_a_5596_);
lean_dec_ref(v_a_5595_);
lean_dec(v_a_5594_);
lean_dec_ref(v_a_5593_);
lean_dec(v_a_5592_);
lean_dec(v_a_5591_);
lean_dec_ref(v_a_5590_);
lean_dec(v_a_5589_);
return v_res_5602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___boxed(lean_object* v_origExpr_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_){
_start:
{
lean_object* v_res_5617_; 
v_res_5617_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_origExpr_5603_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_);
lean_dec(v_a_5615_);
lean_dec_ref(v_a_5614_);
lean_dec(v_a_5613_);
lean_dec_ref(v_a_5612_);
lean_dec(v_a_5611_);
lean_dec_ref(v_a_5610_);
lean_dec(v_a_5609_);
lean_dec_ref(v_a_5608_);
lean_dec(v_a_5607_);
lean_dec(v_a_5606_);
lean_dec_ref(v_a_5605_);
lean_dec(v_a_5604_);
return v_res_5617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(lean_object* v_00_u03b1_5618_, lean_object* v_msg_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v___x_5633_; 
v___x_5633_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___redArg(v_msg_5619_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_);
return v___x_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13___boxed(lean_object* v_00_u03b1_5634_, lean_object* v_msg_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_){
_start:
{
lean_object* v_res_5649_; 
v_res_5649_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(v_00_u03b1_5634_, v_msg_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec_ref(v___y_5640_);
lean_dec(v___y_5639_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
lean_dec(v___y_5636_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16(lean_object* v_00_u03b2_5650_, lean_object* v_m_5651_, lean_object* v_a_5652_){
_start:
{
lean_object* v___x_5653_; 
v___x_5653_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___redArg(v_m_5651_, v_a_5652_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16___boxed(lean_object* v_00_u03b2_5654_, lean_object* v_m_5655_, lean_object* v_a_5656_){
_start:
{
lean_object* v_res_5657_; 
v_res_5657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16(v_00_u03b2_5654_, v_m_5655_, v_a_5656_);
lean_dec_ref(v_a_5656_);
lean_dec_ref(v_m_5655_);
return v_res_5657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17(lean_object* v_00_u03b2_5658_, lean_object* v_m_5659_, lean_object* v_a_5660_, lean_object* v_b_5661_){
_start:
{
lean_object* v___x_5662_; 
v___x_5662_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17___redArg(v_m_5659_, v_a_5660_, v_b_5661_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22(lean_object* v_00_u03b2_5663_, lean_object* v_a_5664_, lean_object* v_x_5665_){
_start:
{
lean_object* v___x_5666_; 
v___x_5666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___redArg(v_a_5664_, v_x_5665_);
return v___x_5666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22___boxed(lean_object* v_00_u03b2_5667_, lean_object* v_a_5668_, lean_object* v_x_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__16_spec__22(v_00_u03b2_5667_, v_a_5668_, v_x_5669_);
lean_dec(v_x_5669_);
lean_dec_ref(v_a_5668_);
return v_res_5670_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24(lean_object* v_00_u03b2_5671_, lean_object* v_a_5672_, lean_object* v_x_5673_){
_start:
{
uint8_t v___x_5674_; 
v___x_5674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___redArg(v_a_5672_, v_x_5673_);
return v___x_5674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24___boxed(lean_object* v_00_u03b2_5675_, lean_object* v_a_5676_, lean_object* v_x_5677_){
_start:
{
uint8_t v_res_5678_; lean_object* v_r_5679_; 
v_res_5678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__24(v_00_u03b2_5675_, v_a_5676_, v_x_5677_);
lean_dec(v_x_5677_);
lean_dec_ref(v_a_5676_);
v_r_5679_ = lean_box(v_res_5678_);
return v_r_5679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25(lean_object* v_00_u03b2_5680_, lean_object* v_data_5681_){
_start:
{
lean_object* v___x_5682_; 
v___x_5682_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25___redArg(v_data_5681_);
return v___x_5682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__26(lean_object* v_00_u03b2_5683_, lean_object* v_a_5684_, lean_object* v_b_5685_, lean_object* v_x_5686_){
_start:
{
lean_object* v___x_5687_; 
v___x_5687_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__26___redArg(v_a_5684_, v_b_5685_, v_x_5686_);
return v___x_5687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30(lean_object* v_00_u03b2_5688_, lean_object* v_i_5689_, lean_object* v_source_5690_, lean_object* v_target_5691_){
_start:
{
lean_object* v___x_5692_; 
v___x_5692_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30___redArg(v_i_5689_, v_source_5690_, v_target_5691_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30_spec__31(lean_object* v_00_u03b2_5693_, lean_object* v_x_5694_, lean_object* v_x_5695_){
_start:
{
lean_object* v___x_5696_; 
v___x_5696_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__17_spec__25_spec__30_spec__31___redArg(v_x_5694_, v_x_5695_);
return v___x_5696_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_CongrInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
}
#ifdef __cplusplus
}
#endif
