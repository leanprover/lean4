// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Canon
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters import Lean.Meta.Tactic.Grind.SynthInstance
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
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_Meta_Grind_instHashableCanonArgKey_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqCanonArgKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getBuiltinInstance_x3f(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isImplicit(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "failed to show that"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "\nis definitionally equal to"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "\nwhile canonicalizing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nusing `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "*1000` heartbeats, `(canonHeartbeats := "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "canon"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 176, 122, 242, 104, 29, 193, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "found using `isDefEqBounded`: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " ===> "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "found "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = ") ↦ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult_default;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonType"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "canonInst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__2_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "canonImplicit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "visit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_isSupport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_isSupport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Tactic.Grind.Canon"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Meta.Tactic.Grind.Canon.0.Lean.Meta.Grind.Canon.canonImpl.visit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__7;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__9;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Canon_canonImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grind canon"};
static const lean_object* l_Lean_Meta_Grind_Canon_canonImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Canon_canonImpl___closed__0_value;
LEAN_EXPORT lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_3_; lean_object* v_toGoalState_4_; lean_object* v_canon_5_; lean_object* v___x_6_; 
v___x_3_ = lean_st_ref_get(v_a_1_);
v_toGoalState_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc_ref(v_toGoalState_4_);
lean_dec(v___x_3_);
v_canon_5_ = lean_ctor_get(v_toGoalState_4_, 1);
lean_inc_ref(v_canon_5_);
lean_dec_ref(v_toGoalState_4_);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v_canon_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg___boxed(lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___redArg(v_a_7_);
lean_dec(v_a_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_toGoalState_22_; lean_object* v_canon_23_; lean_object* v___x_24_; 
v___x_21_ = lean_st_ref_get(v_a_10_);
v_toGoalState_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_toGoalState_22_);
lean_dec(v___x_21_);
v_canon_23_ = lean_ctor_get(v_toGoalState_22_, 1);
lean_inc_ref(v_canon_23_);
lean_dec_ref(v_toGoalState_22_);
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v_canon_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27___boxed(lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_get_x27(v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec(v_a_25_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg(lean_object* v_f_37_, lean_object* v_a_38_){
_start:
{
lean_object* v___x_40_; lean_object* v_toGoalState_41_; lean_object* v_mvarId_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_79_; 
v___x_40_ = lean_st_ref_take(v_a_38_);
v_toGoalState_41_ = lean_ctor_get(v___x_40_, 0);
v_mvarId_42_ = lean_ctor_get(v___x_40_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_79_ == 0)
{
v___x_44_ = v___x_40_;
v_isShared_45_ = v_isSharedCheck_79_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_mvarId_42_);
lean_inc(v_toGoalState_41_);
lean_dec(v___x_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_79_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v_nextDeclIdx_46_; lean_object* v_canon_47_; lean_object* v_enodeMap_48_; lean_object* v_exprs_49_; lean_object* v_parents_50_; lean_object* v_congrTable_51_; lean_object* v_appMap_52_; lean_object* v_indicesFound_53_; lean_object* v_newFacts_54_; uint8_t v_inconsistent_55_; lean_object* v_nextIdx_56_; lean_object* v_newRawFacts_57_; lean_object* v_facts_58_; lean_object* v_extThms_59_; lean_object* v_ematch_60_; lean_object* v_inj_61_; lean_object* v_split_62_; lean_object* v_clean_63_; lean_object* v_sstates_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_78_; 
v_nextDeclIdx_46_ = lean_ctor_get(v_toGoalState_41_, 0);
v_canon_47_ = lean_ctor_get(v_toGoalState_41_, 1);
v_enodeMap_48_ = lean_ctor_get(v_toGoalState_41_, 2);
v_exprs_49_ = lean_ctor_get(v_toGoalState_41_, 3);
v_parents_50_ = lean_ctor_get(v_toGoalState_41_, 4);
v_congrTable_51_ = lean_ctor_get(v_toGoalState_41_, 5);
v_appMap_52_ = lean_ctor_get(v_toGoalState_41_, 6);
v_indicesFound_53_ = lean_ctor_get(v_toGoalState_41_, 7);
v_newFacts_54_ = lean_ctor_get(v_toGoalState_41_, 8);
v_inconsistent_55_ = lean_ctor_get_uint8(v_toGoalState_41_, sizeof(void*)*18);
v_nextIdx_56_ = lean_ctor_get(v_toGoalState_41_, 9);
v_newRawFacts_57_ = lean_ctor_get(v_toGoalState_41_, 10);
v_facts_58_ = lean_ctor_get(v_toGoalState_41_, 11);
v_extThms_59_ = lean_ctor_get(v_toGoalState_41_, 12);
v_ematch_60_ = lean_ctor_get(v_toGoalState_41_, 13);
v_inj_61_ = lean_ctor_get(v_toGoalState_41_, 14);
v_split_62_ = lean_ctor_get(v_toGoalState_41_, 15);
v_clean_63_ = lean_ctor_get(v_toGoalState_41_, 16);
v_sstates_64_ = lean_ctor_get(v_toGoalState_41_, 17);
v_isSharedCheck_78_ = !lean_is_exclusive(v_toGoalState_41_);
if (v_isSharedCheck_78_ == 0)
{
v___x_66_ = v_toGoalState_41_;
v_isShared_67_ = v_isSharedCheck_78_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_sstates_64_);
lean_inc(v_clean_63_);
lean_inc(v_split_62_);
lean_inc(v_inj_61_);
lean_inc(v_ematch_60_);
lean_inc(v_extThms_59_);
lean_inc(v_facts_58_);
lean_inc(v_newRawFacts_57_);
lean_inc(v_nextIdx_56_);
lean_inc(v_newFacts_54_);
lean_inc(v_indicesFound_53_);
lean_inc(v_appMap_52_);
lean_inc(v_congrTable_51_);
lean_inc(v_parents_50_);
lean_inc(v_exprs_49_);
lean_inc(v_enodeMap_48_);
lean_inc(v_canon_47_);
lean_inc(v_nextDeclIdx_46_);
lean_dec(v_toGoalState_41_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_78_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_apply_1(v_f_37_, v_canon_47_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_68_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_nextDeclIdx_46_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_77_, 2, v_enodeMap_48_);
lean_ctor_set(v_reuseFailAlloc_77_, 3, v_exprs_49_);
lean_ctor_set(v_reuseFailAlloc_77_, 4, v_parents_50_);
lean_ctor_set(v_reuseFailAlloc_77_, 5, v_congrTable_51_);
lean_ctor_set(v_reuseFailAlloc_77_, 6, v_appMap_52_);
lean_ctor_set(v_reuseFailAlloc_77_, 7, v_indicesFound_53_);
lean_ctor_set(v_reuseFailAlloc_77_, 8, v_newFacts_54_);
lean_ctor_set(v_reuseFailAlloc_77_, 9, v_nextIdx_56_);
lean_ctor_set(v_reuseFailAlloc_77_, 10, v_newRawFacts_57_);
lean_ctor_set(v_reuseFailAlloc_77_, 11, v_facts_58_);
lean_ctor_set(v_reuseFailAlloc_77_, 12, v_extThms_59_);
lean_ctor_set(v_reuseFailAlloc_77_, 13, v_ematch_60_);
lean_ctor_set(v_reuseFailAlloc_77_, 14, v_inj_61_);
lean_ctor_set(v_reuseFailAlloc_77_, 15, v_split_62_);
lean_ctor_set(v_reuseFailAlloc_77_, 16, v_clean_63_);
lean_ctor_set(v_reuseFailAlloc_77_, 17, v_sstates_64_);
lean_ctor_set_uint8(v_reuseFailAlloc_77_, sizeof(void*)*18, v_inconsistent_55_);
v___x_70_ = v_reuseFailAlloc_77_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_70_);
v___x_72_ = v___x_44_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_mvarId_42_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_st_ref_set(v_a_38_, v___x_72_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg___boxed(lean_object* v_f_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___redArg(v_f_80_, v_a_81_);
lean_dec(v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(lean_object* v_f_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_toGoalState_97_; lean_object* v_mvarId_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_135_; 
v___x_96_ = lean_st_ref_take(v_a_85_);
v_toGoalState_97_ = lean_ctor_get(v___x_96_, 0);
v_mvarId_98_ = lean_ctor_get(v___x_96_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_135_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_135_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_mvarId_98_);
lean_inc(v_toGoalState_97_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_135_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_nextDeclIdx_102_; lean_object* v_canon_103_; lean_object* v_enodeMap_104_; lean_object* v_exprs_105_; lean_object* v_parents_106_; lean_object* v_congrTable_107_; lean_object* v_appMap_108_; lean_object* v_indicesFound_109_; lean_object* v_newFacts_110_; uint8_t v_inconsistent_111_; lean_object* v_nextIdx_112_; lean_object* v_newRawFacts_113_; lean_object* v_facts_114_; lean_object* v_extThms_115_; lean_object* v_ematch_116_; lean_object* v_inj_117_; lean_object* v_split_118_; lean_object* v_clean_119_; lean_object* v_sstates_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_134_; 
v_nextDeclIdx_102_ = lean_ctor_get(v_toGoalState_97_, 0);
v_canon_103_ = lean_ctor_get(v_toGoalState_97_, 1);
v_enodeMap_104_ = lean_ctor_get(v_toGoalState_97_, 2);
v_exprs_105_ = lean_ctor_get(v_toGoalState_97_, 3);
v_parents_106_ = lean_ctor_get(v_toGoalState_97_, 4);
v_congrTable_107_ = lean_ctor_get(v_toGoalState_97_, 5);
v_appMap_108_ = lean_ctor_get(v_toGoalState_97_, 6);
v_indicesFound_109_ = lean_ctor_get(v_toGoalState_97_, 7);
v_newFacts_110_ = lean_ctor_get(v_toGoalState_97_, 8);
v_inconsistent_111_ = lean_ctor_get_uint8(v_toGoalState_97_, sizeof(void*)*18);
v_nextIdx_112_ = lean_ctor_get(v_toGoalState_97_, 9);
v_newRawFacts_113_ = lean_ctor_get(v_toGoalState_97_, 10);
v_facts_114_ = lean_ctor_get(v_toGoalState_97_, 11);
v_extThms_115_ = lean_ctor_get(v_toGoalState_97_, 12);
v_ematch_116_ = lean_ctor_get(v_toGoalState_97_, 13);
v_inj_117_ = lean_ctor_get(v_toGoalState_97_, 14);
v_split_118_ = lean_ctor_get(v_toGoalState_97_, 15);
v_clean_119_ = lean_ctor_get(v_toGoalState_97_, 16);
v_sstates_120_ = lean_ctor_get(v_toGoalState_97_, 17);
v_isSharedCheck_134_ = !lean_is_exclusive(v_toGoalState_97_);
if (v_isSharedCheck_134_ == 0)
{
v___x_122_ = v_toGoalState_97_;
v_isShared_123_ = v_isSharedCheck_134_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_sstates_120_);
lean_inc(v_clean_119_);
lean_inc(v_split_118_);
lean_inc(v_inj_117_);
lean_inc(v_ematch_116_);
lean_inc(v_extThms_115_);
lean_inc(v_facts_114_);
lean_inc(v_newRawFacts_113_);
lean_inc(v_nextIdx_112_);
lean_inc(v_newFacts_110_);
lean_inc(v_indicesFound_109_);
lean_inc(v_appMap_108_);
lean_inc(v_congrTable_107_);
lean_inc(v_parents_106_);
lean_inc(v_exprs_105_);
lean_inc(v_enodeMap_104_);
lean_inc(v_canon_103_);
lean_inc(v_nextDeclIdx_102_);
lean_dec(v_toGoalState_97_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_134_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_apply_1(v_f_84_, v_canon_103_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_124_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_nextDeclIdx_102_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_enodeMap_104_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v_exprs_105_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v_parents_106_);
lean_ctor_set(v_reuseFailAlloc_133_, 5, v_congrTable_107_);
lean_ctor_set(v_reuseFailAlloc_133_, 6, v_appMap_108_);
lean_ctor_set(v_reuseFailAlloc_133_, 7, v_indicesFound_109_);
lean_ctor_set(v_reuseFailAlloc_133_, 8, v_newFacts_110_);
lean_ctor_set(v_reuseFailAlloc_133_, 9, v_nextIdx_112_);
lean_ctor_set(v_reuseFailAlloc_133_, 10, v_newRawFacts_113_);
lean_ctor_set(v_reuseFailAlloc_133_, 11, v_facts_114_);
lean_ctor_set(v_reuseFailAlloc_133_, 12, v_extThms_115_);
lean_ctor_set(v_reuseFailAlloc_133_, 13, v_ematch_116_);
lean_ctor_set(v_reuseFailAlloc_133_, 14, v_inj_117_);
lean_ctor_set(v_reuseFailAlloc_133_, 15, v_split_118_);
lean_ctor_set(v_reuseFailAlloc_133_, 16, v_clean_119_);
lean_ctor_set(v_reuseFailAlloc_133_, 17, v_sstates_120_);
lean_ctor_set_uint8(v_reuseFailAlloc_133_, sizeof(void*)*18, v_inconsistent_111_);
v___x_126_ = v_reuseFailAlloc_133_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_128_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_126_);
v___x_128_ = v___x_100_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_mvarId_98_);
v___x_128_ = v_reuseFailAlloc_132_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_st_ref_set(v_a_85_, v___x_128_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27___boxed(lean_object* v_f_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_modify_x27(v_f_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec(v_a_137_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0(lean_object* v_x_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_apply_11(v_x_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, lean_box(0));
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0___boxed(lean_object* v_x_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0(v_x_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; 
v___f_187_ = lean_alloc_closure((void*)(l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___lam__0___boxed), 12, 9);
lean_closure_set(v___f_187_, 0, v_x_175_);
lean_closure_set(v___f_187_, 1, v___y_176_);
lean_closure_set(v___f_187_, 2, v___y_177_);
lean_closure_set(v___f_187_, 3, v___y_178_);
lean_closure_set(v___f_187_, 4, v___y_179_);
lean_closure_set(v___f_187_, 5, v___y_180_);
lean_closure_set(v___f_187_, 6, v___y_181_);
lean_closure_set(v___f_187_, 7, v___y_182_);
lean_closure_set(v___f_187_, 8, v___y_183_);
v___x_188_ = l___private_Lean_CoreM_0__Lean_Core_withCurrHeartbeatsImp(lean_box(0), v___f_187_, v___y_184_, v___y_185_);
if (lean_obj_tag(v___x_188_) == 0)
{
return v___x_188_;
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg___boxed(lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(v_x_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0(lean_object* v_00_u03b1_210_, lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(v_x_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___boxed(lean_object* v_00_u03b1_224_, lean_object* v_x_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0(v_00_u03b1_224_, v_x_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v_res_237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__1(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__0));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__3(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__2));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__5(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__4));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__7(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__6));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__9(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__8));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__11(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__10));
v___x_255_ = l_Lean_stringToMessageData(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0(lean_object* v_a_256_, lean_object* v_b_257_, lean_object* v_parent_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_261_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_canonHeartbeats_272_; lean_object* v_fileName_273_; lean_object* v_fileMap_274_; lean_object* v_options_275_; lean_object* v_currRecDepth_276_; lean_object* v_maxRecDepth_277_; lean_object* v_ref_278_; lean_object* v_currNamespace_279_; lean_object* v_openDecls_280_; lean_object* v_initHeartbeats_281_; lean_object* v_quotContext_282_; lean_object* v_currMacroScope_283_; uint8_t v_diag_284_; lean_object* v_cancelTk_x3f_285_; uint8_t v_suppressElabErrors_286_; lean_object* v_inheritedTraceOptions_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
v_canonHeartbeats_272_ = lean_ctor_get(v_a_271_, 4);
lean_inc(v_canonHeartbeats_272_);
lean_dec(v_a_271_);
v_fileName_273_ = lean_ctor_get(v___y_267_, 0);
v_fileMap_274_ = lean_ctor_get(v___y_267_, 1);
v_options_275_ = lean_ctor_get(v___y_267_, 2);
v_currRecDepth_276_ = lean_ctor_get(v___y_267_, 3);
v_maxRecDepth_277_ = lean_ctor_get(v___y_267_, 4);
v_ref_278_ = lean_ctor_get(v___y_267_, 5);
v_currNamespace_279_ = lean_ctor_get(v___y_267_, 6);
v_openDecls_280_ = lean_ctor_get(v___y_267_, 7);
v_initHeartbeats_281_ = lean_ctor_get(v___y_267_, 8);
v_quotContext_282_ = lean_ctor_get(v___y_267_, 10);
v_currMacroScope_283_ = lean_ctor_get(v___y_267_, 11);
v_diag_284_ = lean_ctor_get_uint8(v___y_267_, sizeof(void*)*14);
v_cancelTk_x3f_285_ = lean_ctor_get(v___y_267_, 12);
v_suppressElabErrors_286_ = lean_ctor_get_uint8(v___y_267_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_287_ = lean_ctor_get(v___y_267_, 13);
v___x_288_ = lean_unsigned_to_nat(1000u);
v___x_289_ = lean_nat_mul(v_canonHeartbeats_272_, v___x_288_);
lean_inc_ref(v_inheritedTraceOptions_287_);
lean_inc(v_cancelTk_x3f_285_);
lean_inc(v_currMacroScope_283_);
lean_inc(v_quotContext_282_);
lean_inc(v_initHeartbeats_281_);
lean_inc(v_openDecls_280_);
lean_inc(v_currNamespace_279_);
lean_inc(v_ref_278_);
lean_inc(v_maxRecDepth_277_);
lean_inc(v_currRecDepth_276_);
lean_inc_ref(v_options_275_);
lean_inc_ref(v_fileMap_274_);
lean_inc_ref(v_fileName_273_);
v___x_290_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_290_, 0, v_fileName_273_);
lean_ctor_set(v___x_290_, 1, v_fileMap_274_);
lean_ctor_set(v___x_290_, 2, v_options_275_);
lean_ctor_set(v___x_290_, 3, v_currRecDepth_276_);
lean_ctor_set(v___x_290_, 4, v_maxRecDepth_277_);
lean_ctor_set(v___x_290_, 5, v_ref_278_);
lean_ctor_set(v___x_290_, 6, v_currNamespace_279_);
lean_ctor_set(v___x_290_, 7, v_openDecls_280_);
lean_ctor_set(v___x_290_, 8, v_initHeartbeats_281_);
lean_ctor_set(v___x_290_, 9, v___x_289_);
lean_ctor_set(v___x_290_, 10, v_quotContext_282_);
lean_ctor_set(v___x_290_, 11, v_currMacroScope_283_);
lean_ctor_set(v___x_290_, 12, v_cancelTk_x3f_285_);
lean_ctor_set(v___x_290_, 13, v_inheritedTraceOptions_287_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*14, v_diag_284_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*14 + 1, v_suppressElabErrors_286_);
lean_inc(v___y_268_);
lean_inc(v___y_266_);
lean_inc_ref(v___y_265_);
lean_inc_ref(v_b_257_);
lean_inc_ref(v_a_256_);
v___x_291_ = l_Lean_Meta_isDefEqD(v_a_256_, v_b_257_, v___y_265_, v___y_266_, v___x_290_, v___y_268_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_dec(v_canonHeartbeats_272_);
lean_dec(v___y_268_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_parent_258_);
lean_dec_ref(v_b_257_);
lean_dec_ref(v_a_256_);
return v___x_291_;
}
else
{
lean_object* v_a_292_; uint8_t v___x_293_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
v___x_293_ = l_Lean_Exception_isInterrupt(v_a_292_);
if (v___x_293_ == 0)
{
uint8_t v___x_294_; 
v___x_294_ = l_Lean_Exception_isRuntime(v_a_292_);
if (v___x_294_ == 0)
{
lean_dec(v_canonHeartbeats_272_);
lean_dec(v___y_268_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_parent_258_);
lean_dec_ref(v_b_257_);
lean_dec_ref(v_a_256_);
return v___x_291_;
}
else
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_359_; 
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v___x_291_, 0);
lean_dec(v_unused_360_);
v___x_296_ = v___x_291_;
v_isShared_297_ = v_isSharedCheck_359_;
goto v_resetjp_295_;
}
else
{
lean_dec(v___x_291_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_359_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_261_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_350_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_350_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_350_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_350_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint8_t v_verbose_303_; 
v_verbose_303_ = lean_ctor_get_uint8(v_a_299_, sizeof(void*)*11 + 15);
lean_dec(v_a_299_);
if (v_verbose_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_306_; 
lean_del_object(v___x_296_);
lean_dec(v_canonHeartbeats_272_);
lean_dec(v___y_268_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_parent_258_);
lean_dec_ref(v_b_257_);
lean_dec_ref(v_a_256_);
v___x_304_ = lean_box(v___x_293_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_304_);
v___x_306_ = v___x_301_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_del_object(v___x_301_);
v___x_308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__1);
v___x_309_ = l_Lean_indentExpr(v_a_256_);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__3);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_indentExpr(v_b_257_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__5);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Lean_indentExpr(v_parent_258_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__7);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_Nat_reprFast(v_canonHeartbeats_272_);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 3);
lean_ctor_set(v___x_296_, 0, v___x_321_);
v___x_323_ = v___x_296_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_349_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_324_ = l_Lean_MessageData_ofFormat(v___x_323_);
lean_inc_ref(v___x_324_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_320_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__9, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__9);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_324_);
v___x_329_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___closed__11);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_Meta_Grind_reportIssue(v___x_330_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_339_; 
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v___x_331_, 0);
lean_dec(v_unused_340_);
v___x_333_ = v___x_331_;
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
else
{
lean_dec(v___x_331_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_box(v___x_293_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_331_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_331_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_del_object(v___x_296_);
lean_dec(v_canonHeartbeats_272_);
lean_dec(v___y_268_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_parent_258_);
lean_dec_ref(v_b_257_);
lean_dec_ref(v_a_256_);
v_a_351_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_298_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_298_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
}
else
{
lean_dec(v_a_292_);
lean_dec(v_canonHeartbeats_272_);
lean_dec(v___y_268_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_parent_258_);
lean_dec_ref(v_b_257_);
lean_dec_ref(v_a_256_);
return v___x_291_;
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v___y_268_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec_ref(v_parent_258_);
lean_dec_ref(v_b_257_);
lean_dec_ref(v_a_256_);
v_a_361_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_270_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_270_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___boxed(lean_object* v_a_369_, lean_object* v_b_370_, lean_object* v_parent_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0(v_a_369_, v_b_370_, v_parent_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v___y_372_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(lean_object* v_a_384_, lean_object* v_b_385_, lean_object* v_parent_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___f_398_; lean_object* v___x_399_; 
v___f_398_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___lam__0___boxed), 14, 3);
lean_closure_set(v___f_398_, 0, v_a_384_);
lean_closure_set(v___f_398_, 1, v_b_385_);
lean_closure_set(v___f_398_, 2, v_parent_386_);
v___x_399_ = l_Lean_Core_withCurrHeartbeats___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded_spec__0___redArg(v___f_398_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded___boxed(lean_object* v_a_400_, lean_object* v_b_401_, lean_object* v_parent_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(v_a_400_, v_b_401_, v_parent_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(lean_object* v_cls_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_options_421_; uint8_t v_hasTrace_422_; 
v_options_421_ = lean_ctor_get(v___y_419_, 2);
v_hasTrace_422_ = lean_ctor_get_uint8(v_options_421_, sizeof(void*)*1);
if (v_hasTrace_422_ == 0)
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_cls_418_);
v___x_423_ = lean_box(v_hasTrace_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
else
{
lean_object* v_inheritedTraceOptions_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_inheritedTraceOptions_425_ = lean_ctor_get(v___y_419_, 13);
v___x_426_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__1));
v___x_427_ = l_Lean_Name_append(v___x_426_, v_cls_418_);
v___x_428_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_425_, v_options_421_, v___x_427_);
lean_dec(v___x_427_);
v___x_429_ = lean_box(v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___boxed(lean_object* v_cls_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(v_cls_431_, v___y_432_);
lean_dec_ref(v___y_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1(lean_object* v_cls_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(v_cls_435_, v___y_444_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___boxed(lean_object* v_cls_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1(v_cls_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec(v___y_449_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2_spec__3(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_env_468_; lean_object* v___x_469_; lean_object* v_mctx_470_; lean_object* v_lctx_471_; lean_object* v_options_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_467_ = lean_st_ref_get(v___y_465_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v___x_469_ = lean_st_ref_get(v___y_463_);
v_mctx_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_mctx_470_);
lean_dec(v___x_469_);
v_lctx_471_ = lean_ctor_get(v___y_462_, 2);
v_options_472_ = lean_ctor_get(v___y_464_, 2);
lean_inc_ref(v_options_472_);
lean_inc_ref(v_lctx_471_);
v___x_473_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_473_, 0, v_env_468_);
lean_ctor_set(v___x_473_, 1, v_mctx_470_);
lean_ctor_set(v___x_473_, 2, v_lctx_471_);
lean_ctor_set(v___x_473_, 3, v_options_472_);
v___x_474_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_msgData_461_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2_spec__3___boxed(lean_object* v_msgData_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2_spec__3(v_msgData_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_483_; double v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_float_of_nat(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(lean_object* v_cls_488_, lean_object* v_msg_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_ref_495_; lean_object* v___x_496_; lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_541_; 
v_ref_495_ = lean_ctor_get(v___y_492_, 5);
v___x_496_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2_spec__3(v_msg_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_541_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_541_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_541_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v_traceState_502_; lean_object* v_env_503_; lean_object* v_nextMacroScope_504_; lean_object* v_ngen_505_; lean_object* v_auxDeclNGen_506_; lean_object* v_cache_507_; lean_object* v_messages_508_; lean_object* v_infoState_509_; lean_object* v_snapshotTasks_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_540_; 
v___x_501_ = lean_st_ref_take(v___y_493_);
v_traceState_502_ = lean_ctor_get(v___x_501_, 4);
v_env_503_ = lean_ctor_get(v___x_501_, 0);
v_nextMacroScope_504_ = lean_ctor_get(v___x_501_, 1);
v_ngen_505_ = lean_ctor_get(v___x_501_, 2);
v_auxDeclNGen_506_ = lean_ctor_get(v___x_501_, 3);
v_cache_507_ = lean_ctor_get(v___x_501_, 5);
v_messages_508_ = lean_ctor_get(v___x_501_, 6);
v_infoState_509_ = lean_ctor_get(v___x_501_, 7);
v_snapshotTasks_510_ = lean_ctor_get(v___x_501_, 8);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_540_ == 0)
{
v___x_512_ = v___x_501_;
v_isShared_513_ = v_isSharedCheck_540_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snapshotTasks_510_);
lean_inc(v_infoState_509_);
lean_inc(v_messages_508_);
lean_inc(v_cache_507_);
lean_inc(v_traceState_502_);
lean_inc(v_auxDeclNGen_506_);
lean_inc(v_ngen_505_);
lean_inc(v_nextMacroScope_504_);
lean_inc(v_env_503_);
lean_dec(v___x_501_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_540_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint64_t v_tid_514_; lean_object* v_traces_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_539_; 
v_tid_514_ = lean_ctor_get_uint64(v_traceState_502_, sizeof(void*)*1);
v_traces_515_ = lean_ctor_get(v_traceState_502_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_traceState_502_);
if (v_isSharedCheck_539_ == 0)
{
v___x_517_ = v_traceState_502_;
v_isShared_518_ = v_isSharedCheck_539_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_traces_515_);
lean_dec(v_traceState_502_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_539_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; double v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_519_ = lean_box(0);
v___x_520_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0);
v___x_521_ = 0;
v___x_522_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__1));
v___x_523_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_523_, 0, v_cls_488_);
lean_ctor_set(v___x_523_, 1, v___x_519_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
lean_ctor_set_float(v___x_523_, sizeof(void*)*3, v___x_520_);
lean_ctor_set_float(v___x_523_, sizeof(void*)*3 + 8, v___x_520_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*3 + 16, v___x_521_);
v___x_524_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__2));
v___x_525_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v_a_497_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_inc(v_ref_495_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_ref_495_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_PersistentArray_push___redArg(v_traces_515_, v___x_526_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_527_);
v___x_529_ = v___x_517_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_527_);
lean_ctor_set_uint64(v_reuseFailAlloc_538_, sizeof(void*)*1, v_tid_514_);
v___x_529_ = v_reuseFailAlloc_538_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 4, v___x_529_);
v___x_531_ = v___x_512_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_env_503_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_nextMacroScope_504_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_ngen_505_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_auxDeclNGen_506_);
lean_ctor_set(v_reuseFailAlloc_537_, 4, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_537_, 5, v_cache_507_);
lean_ctor_set(v_reuseFailAlloc_537_, 6, v_messages_508_);
lean_ctor_set(v_reuseFailAlloc_537_, 7, v_infoState_509_);
lean_ctor_set(v_reuseFailAlloc_537_, 8, v_snapshotTasks_510_);
v___x_531_ = v_reuseFailAlloc_537_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = lean_st_ref_set(v___y_493_, v___x_531_);
v___x_533_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_533_);
v___x_535_ = v___x_499_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___boxed(lean_object* v_cls_542_, lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(v_cls_542_, v_msg_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_ks_554_; lean_object* v_vs_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_579_; 
v_ks_554_ = lean_ctor_get(v_x_550_, 0);
v_vs_555_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_579_ == 0)
{
v___x_557_ = v_x_550_;
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_vs_555_);
lean_inc(v_ks_554_);
lean_dec(v_x_550_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_579_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_ks_554_);
v___x_560_ = lean_nat_dec_lt(v_x_551_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec(v_x_551_);
v___x_561_ = lean_array_push(v_ks_554_, v_x_552_);
v___x_562_ = lean_array_push(v_vs_555_, v_x_553_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_562_);
lean_ctor_set(v___x_557_, 0, v___x_561_);
v___x_564_ = v___x_557_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
else
{
lean_object* v_k_x27_566_; uint8_t v___x_567_; 
v_k_x27_566_ = lean_array_fget_borrowed(v_ks_554_, v_x_551_);
v___x_567_ = lean_expr_eqv(v_x_552_, v_k_x27_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_569_; 
if (v_isShared_558_ == 0)
{
v___x_569_ = v___x_557_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_ks_554_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_vs_555_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_x_551_, v___x_570_);
lean_dec(v_x_551_);
v_x_550_ = v___x_569_;
v_x_551_ = v___x_571_;
goto _start;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_574_ = lean_array_fset(v_ks_554_, v_x_551_, v_x_552_);
v___x_575_ = lean_array_fset(v_vs_555_, v_x_551_, v_x_553_);
lean_dec(v_x_551_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v___x_575_);
lean_ctor_set(v___x_557_, 0, v___x_574_);
v___x_577_ = v___x_557_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2___redArg(lean_object* v_n_580_, lean_object* v_k_581_, lean_object* v_v_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_584_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2_spec__5___redArg(v_n_580_, v___x_583_, v_k_581_, v_v_582_);
return v___x_584_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; 
v___x_585_ = ((size_t)5ULL);
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_shift_left(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; 
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__0);
v___x_590_ = lean_usize_sub(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg(lean_object* v_x_592_, size_t v_x_593_, size_t v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v_es_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v_j_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_es_597_ = lean_ctor_get(v_x_592_, 0);
v___x_598_ = ((size_t)5ULL);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1);
v___x_601_ = lean_usize_land(v_x_593_, v___x_600_);
v_j_602_ = lean_usize_to_nat(v___x_601_);
v___x_603_ = lean_array_get_size(v_es_597_);
v___x_604_ = lean_nat_dec_lt(v_j_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec(v_j_602_);
lean_dec(v_x_596_);
lean_dec_ref(v_x_595_);
return v_x_592_;
}
else
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_641_; 
lean_inc_ref(v_es_597_);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_x_592_, 0);
lean_dec(v_unused_642_);
v___x_606_ = v_x_592_;
v_isShared_607_ = v_isSharedCheck_641_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_x_592_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_641_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_xs_x27_610_; lean_object* v___y_612_; 
v_v_608_ = lean_array_fget(v_es_597_, v_j_602_);
v___x_609_ = lean_box(0);
v_xs_x27_610_ = lean_array_fset(v_es_597_, v_j_602_, v___x_609_);
switch(lean_obj_tag(v_v_608_))
{
case 0:
{
lean_object* v_key_617_; lean_object* v_val_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_628_; 
v_key_617_ = lean_ctor_get(v_v_608_, 0);
v_val_618_ = lean_ctor_get(v_v_608_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_v_608_);
if (v_isSharedCheck_628_ == 0)
{
v___x_620_ = v_v_608_;
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_val_618_);
lean_inc(v_key_617_);
lean_dec(v_v_608_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_628_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_expr_eqv(v_x_595_, v_key_617_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
lean_del_object(v___x_620_);
v___x_623_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_617_, v_val_618_, v_x_595_, v_x_596_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___y_612_ = v___x_624_;
goto v___jp_611_;
}
else
{
lean_object* v___x_626_; 
lean_dec(v_val_618_);
lean_dec(v_key_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v_x_596_);
lean_ctor_set(v___x_620_, 0, v_x_595_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_x_595_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_x_596_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
v___y_612_ = v___x_626_;
goto v___jp_611_;
}
}
}
}
case 1:
{
lean_object* v_node_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_639_; 
v_node_629_ = lean_ctor_get(v_v_608_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_v_608_);
if (v_isSharedCheck_639_ == 0)
{
v___x_631_ = v_v_608_;
v_isShared_632_ = v_isSharedCheck_639_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_node_629_);
lean_dec(v_v_608_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_639_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_633_ = lean_usize_shift_right(v_x_593_, v___x_598_);
v___x_634_ = lean_usize_add(v_x_594_, v___x_599_);
v___x_635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg(v_node_629_, v___x_633_, v___x_634_, v_x_595_, v_x_596_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_635_);
v___x_637_ = v___x_631_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v___y_612_ = v___x_637_;
goto v___jp_611_;
}
}
}
default: 
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v_x_595_);
lean_ctor_set(v___x_640_, 1, v_x_596_);
v___y_612_ = v___x_640_;
goto v___jp_611_;
}
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_array_fset(v_xs_x27_610_, v_j_602_, v___y_612_);
lean_dec(v_j_602_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_613_);
v___x_615_ = v___x_606_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v_ks_643_; lean_object* v_vs_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_664_; 
v_ks_643_ = lean_ctor_get(v_x_592_, 0);
v_vs_644_ = lean_ctor_get(v_x_592_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_664_ == 0)
{
v___x_646_ = v_x_592_;
v_isShared_647_ = v_isSharedCheck_664_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_vs_644_);
lean_inc(v_ks_643_);
lean_dec(v_x_592_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_664_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_ks_643_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_vs_644_);
v___x_649_ = v_reuseFailAlloc_663_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v_newNode_650_; uint8_t v___y_652_; size_t v___x_658_; uint8_t v___x_659_; 
v_newNode_650_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2___redArg(v___x_649_, v_x_595_, v_x_596_);
v___x_658_ = ((size_t)7ULL);
v___x_659_ = lean_usize_dec_le(v___x_658_, v_x_594_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_650_);
v___x_661_ = lean_unsigned_to_nat(4u);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
v___y_652_ = v___x_662_;
goto v___jp_651_;
}
else
{
v___y_652_ = v___x_659_;
goto v___jp_651_;
}
v___jp_651_:
{
if (v___y_652_ == 0)
{
lean_object* v_ks_653_; lean_object* v_vs_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_ks_653_ = lean_ctor_get(v_newNode_650_, 0);
lean_inc_ref(v_ks_653_);
v_vs_654_ = lean_ctor_get(v_newNode_650_, 1);
lean_inc_ref(v_vs_654_);
lean_dec_ref(v_newNode_650_);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__2);
v___x_657_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___redArg(v_x_594_, v_ks_653_, v_vs_654_, v___x_655_, v___x_656_);
lean_dec_ref(v_vs_654_);
lean_dec_ref(v_ks_653_);
return v___x_657_;
}
else
{
return v_newNode_650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___redArg(size_t v_depth_665_, lean_object* v_keys_666_, lean_object* v_vals_667_, lean_object* v_i_668_, lean_object* v_entries_669_){
_start:
{
lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_670_ = lean_array_get_size(v_keys_666_);
v___x_671_ = lean_nat_dec_lt(v_i_668_, v___x_670_);
if (v___x_671_ == 0)
{
lean_dec(v_i_668_);
return v_entries_669_;
}
else
{
lean_object* v_k_672_; lean_object* v_v_673_; uint64_t v___x_674_; size_t v_h_675_; size_t v___x_676_; lean_object* v___x_677_; size_t v___x_678_; size_t v___x_679_; size_t v___x_680_; size_t v_h_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_k_672_ = lean_array_fget_borrowed(v_keys_666_, v_i_668_);
v_v_673_ = lean_array_fget_borrowed(v_vals_667_, v_i_668_);
v___x_674_ = l_Lean_Expr_hash(v_k_672_);
v_h_675_ = lean_uint64_to_usize(v___x_674_);
v___x_676_ = ((size_t)5ULL);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_sub(v_depth_665_, v___x_678_);
v___x_680_ = lean_usize_mul(v___x_676_, v___x_679_);
v_h_681_ = lean_usize_shift_right(v_h_675_, v___x_680_);
v___x_682_ = lean_nat_add(v_i_668_, v___x_677_);
lean_dec(v_i_668_);
lean_inc(v_v_673_);
lean_inc(v_k_672_);
v___x_683_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg(v_entries_669_, v_h_681_, v_depth_665_, v_k_672_, v_v_673_);
v_i_668_ = v___x_682_;
v_entries_669_ = v___x_683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_685_, lean_object* v_keys_686_, lean_object* v_vals_687_, lean_object* v_i_688_, lean_object* v_entries_689_){
_start:
{
size_t v_depth_boxed_690_; lean_object* v_res_691_; 
v_depth_boxed_690_ = lean_unbox_usize(v_depth_685_);
lean_dec(v_depth_685_);
v_res_691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___redArg(v_depth_boxed_690_, v_keys_686_, v_vals_687_, v_i_688_, v_entries_689_);
lean_dec_ref(v_vals_687_);
lean_dec_ref(v_keys_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___boxed(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
size_t v_x_34694__boxed_697_; size_t v_x_34695__boxed_698_; lean_object* v_res_699_; 
v_x_34694__boxed_697_ = lean_unbox_usize(v_x_693_);
lean_dec(v_x_693_);
v_x_34695__boxed_698_ = lean_unbox_usize(v_x_694_);
lean_dec(v_x_694_);
v_res_699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg(v_x_692_, v_x_34694__boxed_697_, v_x_34695__boxed_698_, v_x_695_, v_x_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0___redArg(lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
uint64_t v___x_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_703_ = l_Lean_Expr_hash(v_x_701_);
v___x_704_ = lean_uint64_to_usize(v___x_703_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg(v_x_700_, v___x_704_, v___x_705_, v_x_701_, v_x_702_);
return v___x_706_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__5(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__4));
v___x_716_ = l_Lean_stringToMessageData(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__6));
v___x_719_ = l_Lean_stringToMessageData(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__9(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__8));
v___x_722_ = l_Lean_stringToMessageData(v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq(lean_object* v_parent_723_, uint8_t v_useIsDefEqBounded_724_, lean_object* v_e_725_, lean_object* v_c_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
lean_inc_ref(v_c_726_);
lean_inc_ref(v_e_725_);
v___x_738_ = l_Lean_Meta_isExprDefEq(v_e_725_, v_c_726_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; uint8_t v___x_740_; uint8_t v___x_741_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
v___x_740_ = 1;
v___x_741_ = lean_unbox(v_a_739_);
if (v___x_741_ == 0)
{
if (v_useIsDefEqBounded_724_ == 0)
{
lean_dec(v_a_739_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
lean_dec_ref(v_parent_723_);
return v___x_738_;
}
else
{
lean_object* v___x_742_; 
lean_dec_ref(v___x_738_);
lean_inc(v_a_736_);
lean_inc_ref(v_a_735_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
lean_inc(v_a_732_);
lean_inc_ref(v_a_731_);
lean_inc(v_a_730_);
lean_inc_ref(v_a_729_);
lean_inc(v_a_728_);
lean_inc(v_a_727_);
lean_inc_ref(v_c_726_);
lean_inc_ref(v_e_725_);
v___x_742_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_isDefEqBounded(v_e_725_, v_c_726_, v_parent_723_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_848_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_848_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_848_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_848_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; 
v___x_747_ = lean_unbox(v_a_743_);
lean_dec(v_a_743_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; 
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v_a_739_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_739_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_object* v___x_751_; lean_object* v_toGoalState_752_; lean_object* v_canon_753_; lean_object* v_mvarId_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_846_; 
lean_del_object(v___x_745_);
lean_dec(v_a_739_);
v___x_751_ = lean_st_ref_take(v_a_727_);
v_toGoalState_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc_ref(v_toGoalState_752_);
v_canon_753_ = lean_ctor_get(v_toGoalState_752_, 1);
lean_inc_ref(v_canon_753_);
v_mvarId_754_ = lean_ctor_get(v___x_751_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_847_);
v___x_756_ = v___x_751_;
v_isShared_757_ = v_isSharedCheck_846_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_mvarId_754_);
lean_dec(v___x_751_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_846_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_nextDeclIdx_758_; lean_object* v_enodeMap_759_; lean_object* v_exprs_760_; lean_object* v_parents_761_; lean_object* v_congrTable_762_; lean_object* v_appMap_763_; lean_object* v_indicesFound_764_; lean_object* v_newFacts_765_; uint8_t v_inconsistent_766_; lean_object* v_nextIdx_767_; lean_object* v_newRawFacts_768_; lean_object* v_facts_769_; lean_object* v_extThms_770_; lean_object* v_ematch_771_; lean_object* v_inj_772_; lean_object* v_split_773_; lean_object* v_clean_774_; lean_object* v_sstates_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_844_; 
v_nextDeclIdx_758_ = lean_ctor_get(v_toGoalState_752_, 0);
v_enodeMap_759_ = lean_ctor_get(v_toGoalState_752_, 2);
v_exprs_760_ = lean_ctor_get(v_toGoalState_752_, 3);
v_parents_761_ = lean_ctor_get(v_toGoalState_752_, 4);
v_congrTable_762_ = lean_ctor_get(v_toGoalState_752_, 5);
v_appMap_763_ = lean_ctor_get(v_toGoalState_752_, 6);
v_indicesFound_764_ = lean_ctor_get(v_toGoalState_752_, 7);
v_newFacts_765_ = lean_ctor_get(v_toGoalState_752_, 8);
v_inconsistent_766_ = lean_ctor_get_uint8(v_toGoalState_752_, sizeof(void*)*18);
v_nextIdx_767_ = lean_ctor_get(v_toGoalState_752_, 9);
v_newRawFacts_768_ = lean_ctor_get(v_toGoalState_752_, 10);
v_facts_769_ = lean_ctor_get(v_toGoalState_752_, 11);
v_extThms_770_ = lean_ctor_get(v_toGoalState_752_, 12);
v_ematch_771_ = lean_ctor_get(v_toGoalState_752_, 13);
v_inj_772_ = lean_ctor_get(v_toGoalState_752_, 14);
v_split_773_ = lean_ctor_get(v_toGoalState_752_, 15);
v_clean_774_ = lean_ctor_get(v_toGoalState_752_, 16);
v_sstates_775_ = lean_ctor_get(v_toGoalState_752_, 17);
v_isSharedCheck_844_ = !lean_is_exclusive(v_toGoalState_752_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_toGoalState_752_, 1);
lean_dec(v_unused_845_);
v___x_777_ = v_toGoalState_752_;
v_isShared_778_ = v_isSharedCheck_844_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_sstates_775_);
lean_inc(v_clean_774_);
lean_inc(v_split_773_);
lean_inc(v_inj_772_);
lean_inc(v_ematch_771_);
lean_inc(v_extThms_770_);
lean_inc(v_facts_769_);
lean_inc(v_newRawFacts_768_);
lean_inc(v_nextIdx_767_);
lean_inc(v_newFacts_765_);
lean_inc(v_indicesFound_764_);
lean_inc(v_appMap_763_);
lean_inc(v_congrTable_762_);
lean_inc(v_parents_761_);
lean_inc(v_exprs_760_);
lean_inc(v_enodeMap_759_);
lean_inc(v_nextDeclIdx_758_);
lean_dec(v_toGoalState_752_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_844_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_argMap_779_; lean_object* v_canon_780_; lean_object* v_proofCanon_781_; lean_object* v_canonArg_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_843_; 
v_argMap_779_ = lean_ctor_get(v_canon_753_, 0);
v_canon_780_ = lean_ctor_get(v_canon_753_, 1);
v_proofCanon_781_ = lean_ctor_get(v_canon_753_, 2);
v_canonArg_782_ = lean_ctor_get(v_canon_753_, 3);
v_isSharedCheck_843_ = !lean_is_exclusive(v_canon_753_);
if (v_isSharedCheck_843_ == 0)
{
v___x_784_ = v_canon_753_;
v_isShared_785_ = v_isSharedCheck_843_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_canonArg_782_);
lean_inc(v_proofCanon_781_);
lean_inc(v_canon_780_);
lean_inc(v_argMap_779_);
lean_dec(v_canon_753_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_843_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_inc_ref(v_c_726_);
lean_inc_ref(v_e_725_);
v___x_786_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0___redArg(v_canon_780_, v_e_725_, v_c_726_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_argMap_779_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_proofCanon_781_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_canonArg_782_);
v___x_788_ = v_reuseFailAlloc_842_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_788_);
v___x_790_ = v___x_777_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_nextDeclIdx_758_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_enodeMap_759_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v_exprs_760_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v_parents_761_);
lean_ctor_set(v_reuseFailAlloc_841_, 5, v_congrTable_762_);
lean_ctor_set(v_reuseFailAlloc_841_, 6, v_appMap_763_);
lean_ctor_set(v_reuseFailAlloc_841_, 7, v_indicesFound_764_);
lean_ctor_set(v_reuseFailAlloc_841_, 8, v_newFacts_765_);
lean_ctor_set(v_reuseFailAlloc_841_, 9, v_nextIdx_767_);
lean_ctor_set(v_reuseFailAlloc_841_, 10, v_newRawFacts_768_);
lean_ctor_set(v_reuseFailAlloc_841_, 11, v_facts_769_);
lean_ctor_set(v_reuseFailAlloc_841_, 12, v_extThms_770_);
lean_ctor_set(v_reuseFailAlloc_841_, 13, v_ematch_771_);
lean_ctor_set(v_reuseFailAlloc_841_, 14, v_inj_772_);
lean_ctor_set(v_reuseFailAlloc_841_, 15, v_split_773_);
lean_ctor_set(v_reuseFailAlloc_841_, 16, v_clean_774_);
lean_ctor_set(v_reuseFailAlloc_841_, 17, v_sstates_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_841_, sizeof(void*)*18, v_inconsistent_766_);
v___x_790_ = v_reuseFailAlloc_841_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_790_);
v___x_792_ = v___x_756_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_mvarId_754_);
v___x_792_ = v_reuseFailAlloc_840_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_839_; 
v___x_793_ = lean_st_ref_set(v_a_727_, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3));
v___x_795_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(v___x_794_, v_a_735_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_839_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_839_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_839_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
uint8_t v___x_800_; 
v___x_800_ = lean_unbox(v_a_796_);
lean_dec(v_a_796_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
v___x_801_ = lean_box(v___x_740_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_801_);
v___x_803_ = v___x_798_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
lean_object* v___x_805_; 
lean_del_object(v___x_798_);
v___x_805_ = l_Lean_Meta_Grind_updateLastTag(v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec_ref(v___x_805_);
v___x_806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__5, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__5);
v___x_807_ = l_Lean_MessageData_ofExpr(v_e_725_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_MessageData_ofExpr(v_c_726_);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(v___x_794_, v___x_812_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_813_, 0);
lean_dec(v_unused_822_);
v___x_815_ = v___x_813_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_dec(v___x_813_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_box(v___x_740_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_813_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
v_a_831_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_805_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_805_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
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
}
else
{
lean_dec(v_a_739_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
return v___x_742_;
}
}
}
else
{
lean_object* v___x_849_; lean_object* v_toGoalState_850_; lean_object* v_canon_851_; lean_object* v_mvarId_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___x_738_);
lean_dec(v_a_739_);
lean_dec_ref(v_parent_723_);
v___x_849_ = lean_st_ref_take(v_a_727_);
v_toGoalState_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_toGoalState_850_);
v_canon_851_ = lean_ctor_get(v_toGoalState_850_, 1);
lean_inc_ref(v_canon_851_);
v_mvarId_852_ = lean_ctor_get(v___x_849_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v___x_849_, 0);
lean_dec(v_unused_945_);
v___x_854_ = v___x_849_;
v_isShared_855_ = v_isSharedCheck_944_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_mvarId_852_);
lean_dec(v___x_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_944_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_nextDeclIdx_856_; lean_object* v_enodeMap_857_; lean_object* v_exprs_858_; lean_object* v_parents_859_; lean_object* v_congrTable_860_; lean_object* v_appMap_861_; lean_object* v_indicesFound_862_; lean_object* v_newFacts_863_; uint8_t v_inconsistent_864_; lean_object* v_nextIdx_865_; lean_object* v_newRawFacts_866_; lean_object* v_facts_867_; lean_object* v_extThms_868_; lean_object* v_ematch_869_; lean_object* v_inj_870_; lean_object* v_split_871_; lean_object* v_clean_872_; lean_object* v_sstates_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_942_; 
v_nextDeclIdx_856_ = lean_ctor_get(v_toGoalState_850_, 0);
v_enodeMap_857_ = lean_ctor_get(v_toGoalState_850_, 2);
v_exprs_858_ = lean_ctor_get(v_toGoalState_850_, 3);
v_parents_859_ = lean_ctor_get(v_toGoalState_850_, 4);
v_congrTable_860_ = lean_ctor_get(v_toGoalState_850_, 5);
v_appMap_861_ = lean_ctor_get(v_toGoalState_850_, 6);
v_indicesFound_862_ = lean_ctor_get(v_toGoalState_850_, 7);
v_newFacts_863_ = lean_ctor_get(v_toGoalState_850_, 8);
v_inconsistent_864_ = lean_ctor_get_uint8(v_toGoalState_850_, sizeof(void*)*18);
v_nextIdx_865_ = lean_ctor_get(v_toGoalState_850_, 9);
v_newRawFacts_866_ = lean_ctor_get(v_toGoalState_850_, 10);
v_facts_867_ = lean_ctor_get(v_toGoalState_850_, 11);
v_extThms_868_ = lean_ctor_get(v_toGoalState_850_, 12);
v_ematch_869_ = lean_ctor_get(v_toGoalState_850_, 13);
v_inj_870_ = lean_ctor_get(v_toGoalState_850_, 14);
v_split_871_ = lean_ctor_get(v_toGoalState_850_, 15);
v_clean_872_ = lean_ctor_get(v_toGoalState_850_, 16);
v_sstates_873_ = lean_ctor_get(v_toGoalState_850_, 17);
v_isSharedCheck_942_ = !lean_is_exclusive(v_toGoalState_850_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v_toGoalState_850_, 1);
lean_dec(v_unused_943_);
v___x_875_ = v_toGoalState_850_;
v_isShared_876_ = v_isSharedCheck_942_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_sstates_873_);
lean_inc(v_clean_872_);
lean_inc(v_split_871_);
lean_inc(v_inj_870_);
lean_inc(v_ematch_869_);
lean_inc(v_extThms_868_);
lean_inc(v_facts_867_);
lean_inc(v_newRawFacts_866_);
lean_inc(v_nextIdx_865_);
lean_inc(v_newFacts_863_);
lean_inc(v_indicesFound_862_);
lean_inc(v_appMap_861_);
lean_inc(v_congrTable_860_);
lean_inc(v_parents_859_);
lean_inc(v_exprs_858_);
lean_inc(v_enodeMap_857_);
lean_inc(v_nextDeclIdx_856_);
lean_dec(v_toGoalState_850_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_942_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_argMap_877_; lean_object* v_canon_878_; lean_object* v_proofCanon_879_; lean_object* v_canonArg_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_941_; 
v_argMap_877_ = lean_ctor_get(v_canon_851_, 0);
v_canon_878_ = lean_ctor_get(v_canon_851_, 1);
v_proofCanon_879_ = lean_ctor_get(v_canon_851_, 2);
v_canonArg_880_ = lean_ctor_get(v_canon_851_, 3);
v_isSharedCheck_941_ = !lean_is_exclusive(v_canon_851_);
if (v_isSharedCheck_941_ == 0)
{
v___x_882_ = v_canon_851_;
v_isShared_883_ = v_isSharedCheck_941_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_canonArg_880_);
lean_inc(v_proofCanon_879_);
lean_inc(v_canon_878_);
lean_inc(v_argMap_877_);
lean_dec(v_canon_851_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_941_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_inc_ref(v_c_726_);
lean_inc_ref(v_e_725_);
v___x_884_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0___redArg(v_canon_878_, v_e_725_, v_c_726_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_argMap_877_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_proofCanon_879_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_canonArg_880_);
v___x_886_ = v_reuseFailAlloc_940_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_886_);
v___x_888_ = v___x_875_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_nextDeclIdx_856_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_enodeMap_857_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_exprs_858_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v_parents_859_);
lean_ctor_set(v_reuseFailAlloc_939_, 5, v_congrTable_860_);
lean_ctor_set(v_reuseFailAlloc_939_, 6, v_appMap_861_);
lean_ctor_set(v_reuseFailAlloc_939_, 7, v_indicesFound_862_);
lean_ctor_set(v_reuseFailAlloc_939_, 8, v_newFacts_863_);
lean_ctor_set(v_reuseFailAlloc_939_, 9, v_nextIdx_865_);
lean_ctor_set(v_reuseFailAlloc_939_, 10, v_newRawFacts_866_);
lean_ctor_set(v_reuseFailAlloc_939_, 11, v_facts_867_);
lean_ctor_set(v_reuseFailAlloc_939_, 12, v_extThms_868_);
lean_ctor_set(v_reuseFailAlloc_939_, 13, v_ematch_869_);
lean_ctor_set(v_reuseFailAlloc_939_, 14, v_inj_870_);
lean_ctor_set(v_reuseFailAlloc_939_, 15, v_split_871_);
lean_ctor_set(v_reuseFailAlloc_939_, 16, v_clean_872_);
lean_ctor_set(v_reuseFailAlloc_939_, 17, v_sstates_873_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*18, v_inconsistent_864_);
v___x_888_ = v_reuseFailAlloc_939_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_888_);
v___x_890_ = v___x_854_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_mvarId_852_);
v___x_890_ = v_reuseFailAlloc_938_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_937_; 
v___x_891_ = lean_st_ref_set(v_a_727_, v___x_890_);
v___x_892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3));
v___x_893_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(v___x_892_, v_a_735_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_937_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_937_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_937_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
uint8_t v___x_898_; 
v___x_898_ = lean_unbox(v_a_894_);
lean_dec(v_a_894_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_901_; 
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
v___x_899_ = lean_box(v___x_740_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v___x_903_; 
lean_del_object(v___x_896_);
v___x_903_ = l_Lean_Meta_Grind_updateLastTag(v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref(v___x_903_);
v___x_904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__9, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__9);
v___x_905_ = l_Lean_MessageData_ofExpr(v_e_725_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__7);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_MessageData_ofExpr(v_c_726_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(v___x_892_, v___x_910_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v___x_911_, 0);
lean_dec(v_unused_920_);
v___x_913_ = v___x_911_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_911_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_box(v___x_740_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_911_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_911_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
v_a_929_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_903_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_903_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
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
else
{
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_c_726_);
lean_dec_ref(v_e_725_);
lean_dec_ref(v_parent_723_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___boxed(lean_object* v_parent_946_, lean_object* v_useIsDefEqBounded_947_, lean_object* v_e_948_, lean_object* v_c_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
uint8_t v_useIsDefEqBounded_boxed_961_; lean_object* v_res_962_; 
v_useIsDefEqBounded_boxed_961_ = lean_unbox(v_useIsDefEqBounded_947_);
v_res_962_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq(v_parent_946_, v_useIsDefEqBounded_boxed_961_, v_e_948_, v_c_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0(lean_object* v_00_u03b2_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0___redArg(v_x_964_, v_x_965_, v_x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2(lean_object* v_cls_968_, lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(v_cls_968_, v_msg_969_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___boxed(lean_object* v_cls_982_, lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2(v_cls_982_, v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec(v___y_984_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0(lean_object* v_00_u03b2_996_, lean_object* v_x_997_, size_t v_x_998_, size_t v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg(v_x_997_, v_x_998_, v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
size_t v_x_35328__boxed_1009_; size_t v_x_35329__boxed_1010_; lean_object* v_res_1011_; 
v_x_35328__boxed_1009_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_x_35329__boxed_1010_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_res_1011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0(v_00_u03b2_1003_, v_x_1004_, v_x_35328__boxed_1009_, v_x_35329__boxed_1010_, v_x_1007_, v_x_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1012_, lean_object* v_n_1013_, lean_object* v_k_1014_, lean_object* v_v_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2___redArg(v_n_1013_, v_k_1014_, v_v_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1017_, size_t v_depth_1018_, lean_object* v_keys_1019_, lean_object* v_vals_1020_, lean_object* v_heq_1021_, lean_object* v_i_1022_, lean_object* v_entries_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___redArg(v_depth_1018_, v_keys_1019_, v_vals_1020_, v_i_1022_, v_entries_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_depth_1026_, lean_object* v_keys_1027_, lean_object* v_vals_1028_, lean_object* v_heq_1029_, lean_object* v_i_1030_, lean_object* v_entries_1031_){
_start:
{
size_t v_depth_boxed_1032_; lean_object* v_res_1033_; 
v_depth_boxed_1032_ = lean_unbox_usize(v_depth_1026_);
lean_dec(v_depth_1026_);
v_res_1033_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__3(v_00_u03b2_1025_, v_depth_boxed_1032_, v_keys_1027_, v_vals_1028_, v_heq_1029_, v_i_1030_, v_entries_1031_);
lean_dec_ref(v_vals_1028_);
lean_dec_ref(v_keys_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1035_, v_x_1036_, v_x_1037_, v_x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg(lean_object* v_a_1043_, lean_object* v_parent_1044_, uint8_t v_useIsDefEqBounded_1045_, lean_object* v_e_1046_, lean_object* v_as_x27_1047_, lean_object* v_b_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
if (lean_obj_tag(v_as_x27_1047_) == 0)
{
lean_object* v___x_1060_; 
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v_e_1046_);
lean_dec_ref(v_parent_1044_);
lean_dec_ref(v_a_1043_);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_b_1048_);
return v___x_1060_;
}
else
{
lean_object* v_head_1061_; lean_object* v_tail_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_b_1048_);
v_head_1061_ = lean_ctor_get(v_as_x27_1047_, 0);
lean_inc(v_head_1061_);
v_tail_1062_ = lean_ctor_get(v_as_x27_1047_, 1);
lean_inc(v_tail_1062_);
lean_dec_ref(v_as_x27_1047_);
v_fst_1063_ = lean_ctor_get(v_head_1061_, 0);
v_snd_1064_ = lean_ctor_get(v_head_1061_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_head_1061_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1066_ = v_head_1061_;
v_isShared_1067_ = v_isSharedCheck_1105_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_inc(v_fst_1063_);
lean_dec(v_head_1061_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1105_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; 
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc_ref(v_a_1043_);
v___x_1068_ = l_Lean_Meta_isDefEqD(v_a_1043_, v_snd_1064_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = lean_box(0);
v___x_1071_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg___closed__0));
v___x_1072_ = lean_unbox(v_a_1069_);
lean_dec(v_a_1069_);
if (v___x_1072_ == 0)
{
lean_del_object(v___x_1066_);
lean_dec(v_fst_1063_);
v_as_x27_1047_ = v_tail_1062_;
v_b_1048_ = v___x_1071_;
goto _start;
}
else
{
lean_object* v___x_1074_; 
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
lean_inc(v___y_1054_);
lean_inc_ref(v___y_1053_);
lean_inc(v___y_1052_);
lean_inc_ref(v___y_1051_);
lean_inc(v___y_1050_);
lean_inc(v___y_1049_);
lean_inc(v_fst_1063_);
lean_inc_ref(v_e_1046_);
lean_inc_ref(v_parent_1044_);
v___x_1074_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq(v_parent_1044_, v_useIsDefEqBounded_1045_, v_e_1046_, v_fst_1063_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1088_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1088_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1088_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_unbox(v_a_1075_);
lean_dec(v_a_1075_);
if (v___x_1079_ == 0)
{
lean_del_object(v___x_1077_);
lean_del_object(v___x_1066_);
lean_dec(v_fst_1063_);
v_as_x27_1047_ = v_tail_1062_;
v_b_1048_ = v___x_1071_;
goto _start;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_dec(v_tail_1062_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v_e_1046_);
lean_dec_ref(v_parent_1044_);
lean_dec_ref(v_a_1043_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_fst_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1070_);
lean_ctor_set(v___x_1066_, 0, v___x_1081_);
v___x_1083_ = v___x_1066_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1070_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1083_);
v___x_1085_ = v___x_1077_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_del_object(v___x_1066_);
lean_dec(v_fst_1063_);
lean_dec(v_tail_1062_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v_e_1046_);
lean_dec_ref(v_parent_1044_);
lean_dec_ref(v_a_1043_);
v_a_1089_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1074_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1074_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_del_object(v___x_1066_);
lean_dec(v_fst_1063_);
lean_dec(v_tail_1062_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v_e_1046_);
lean_dec_ref(v_parent_1044_);
lean_dec_ref(v_a_1043_);
v_a_1097_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1068_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1068_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_a_1106_ = _args[0];
lean_object* v_parent_1107_ = _args[1];
lean_object* v_useIsDefEqBounded_1108_ = _args[2];
lean_object* v_e_1109_ = _args[3];
lean_object* v_as_x27_1110_ = _args[4];
lean_object* v_b_1111_ = _args[5];
lean_object* v___y_1112_ = _args[6];
lean_object* v___y_1113_ = _args[7];
lean_object* v___y_1114_ = _args[8];
lean_object* v___y_1115_ = _args[9];
lean_object* v___y_1116_ = _args[10];
lean_object* v___y_1117_ = _args[11];
lean_object* v___y_1118_ = _args[12];
lean_object* v___y_1119_ = _args[13];
lean_object* v___y_1120_ = _args[14];
lean_object* v___y_1121_ = _args[15];
lean_object* v___y_1122_ = _args[16];
_start:
{
uint8_t v_useIsDefEqBounded_boxed_1123_; lean_object* v_res_1124_; 
v_useIsDefEqBounded_boxed_1123_ = lean_unbox(v_useIsDefEqBounded_1108_);
v_res_1124_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg(v_a_1106_, v_parent_1107_, v_useIsDefEqBounded_boxed_1123_, v_e_1109_, v_as_x27_1110_, v_b_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v_ks_1129_; lean_object* v_vs_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1159_; 
v_ks_1129_ = lean_ctor_get(v_x_1125_, 0);
v_vs_1130_ = lean_ctor_get(v_x_1125_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_x_1125_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1132_ = v_x_1125_;
v_isShared_1133_ = v_isSharedCheck_1159_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_vs_1130_);
lean_inc(v_ks_1129_);
lean_dec(v_x_1125_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1159_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint8_t v___y_1135_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_array_get_size(v_ks_1129_);
v___x_1148_ = lean_nat_dec_lt(v_x_1126_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_del_object(v___x_1132_);
lean_dec(v_x_1126_);
v___x_1149_ = lean_array_push(v_ks_1129_, v_x_1127_);
v___x_1150_ = lean_array_push(v_vs_1130_, v_x_1128_);
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v_k_x27_1154_; lean_object* v_fst_1155_; lean_object* v_snd_1156_; uint8_t v___x_1157_; 
v_fst_1152_ = lean_ctor_get(v_x_1127_, 0);
v_snd_1153_ = lean_ctor_get(v_x_1127_, 1);
v_k_x27_1154_ = lean_array_fget_borrowed(v_ks_1129_, v_x_1126_);
v_fst_1155_ = lean_ctor_get(v_k_x27_1154_, 0);
v_snd_1156_ = lean_ctor_get(v_k_x27_1154_, 1);
v___x_1157_ = lean_expr_eqv(v_fst_1152_, v_fst_1155_);
if (v___x_1157_ == 0)
{
v___y_1135_ = v___x_1157_;
goto v___jp_1134_;
}
else
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_nat_dec_eq(v_snd_1153_, v_snd_1156_);
v___y_1135_ = v___x_1158_;
goto v___jp_1134_;
}
}
v___jp_1134_:
{
if (v___y_1135_ == 0)
{
lean_object* v___x_1137_; 
if (v_isShared_1133_ == 0)
{
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_ks_1129_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_vs_1130_);
v___x_1137_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = lean_nat_add(v_x_1126_, v___x_1138_);
lean_dec(v_x_1126_);
v_x_1125_ = v___x_1137_;
v_x_1126_ = v___x_1139_;
goto _start;
}
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = lean_array_fset(v_ks_1129_, v_x_1126_, v_x_1127_);
v___x_1143_ = lean_array_fset(v_vs_1130_, v_x_1126_, v_x_1128_);
lean_dec(v_x_1126_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1143_);
lean_ctor_set(v___x_1132_, 0, v___x_1142_);
v___x_1145_ = v___x_1132_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1160_, lean_object* v_k_1161_, lean_object* v_v_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1_spec__4___redArg(v_n_1160_, v___x_1163_, v_k_1161_, v_v_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg(lean_object* v_x_1166_, size_t v_x_1167_, size_t v_x_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1166_) == 0)
{
lean_object* v_es_1171_; size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v_j_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_es_1171_ = lean_ctor_get(v_x_1166_, 0);
v___x_1172_ = ((size_t)5ULL);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1);
v___x_1175_ = lean_usize_land(v_x_1167_, v___x_1174_);
v_j_1176_ = lean_usize_to_nat(v___x_1175_);
v___x_1177_ = lean_array_get_size(v_es_1171_);
v___x_1178_ = lean_nat_dec_lt(v_j_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_j_1176_);
lean_dec(v_x_1170_);
lean_dec_ref(v_x_1169_);
return v_x_1166_;
}
else
{
lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1222_; 
lean_inc_ref(v_es_1171_);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1166_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_x_1166_, 0);
lean_dec(v_unused_1223_);
v___x_1180_ = v_x_1166_;
v_isShared_1181_ = v_isSharedCheck_1222_;
goto v_resetjp_1179_;
}
else
{
lean_dec(v_x_1166_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1222_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_v_1182_; lean_object* v___x_1183_; lean_object* v_xs_x27_1184_; lean_object* v___y_1186_; 
v_v_1182_ = lean_array_fget(v_es_1171_, v_j_1176_);
v___x_1183_ = lean_box(0);
v_xs_x27_1184_ = lean_array_fset(v_es_1171_, v_j_1176_, v___x_1183_);
switch(lean_obj_tag(v_v_1182_))
{
case 0:
{
lean_object* v_key_1191_; lean_object* v_val_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1209_; 
v_key_1191_ = lean_ctor_get(v_v_1182_, 0);
v_val_1192_ = lean_ctor_get(v_v_1182_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_v_1182_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1194_ = v_v_1182_;
v_isShared_1195_ = v_isSharedCheck_1209_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_val_1192_);
lean_inc(v_key_1191_);
lean_dec(v_v_1182_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1209_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
uint8_t v___y_1197_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; uint8_t v___x_1207_; 
v_fst_1203_ = lean_ctor_get(v_x_1169_, 0);
v_snd_1204_ = lean_ctor_get(v_x_1169_, 1);
v_fst_1205_ = lean_ctor_get(v_key_1191_, 0);
v_snd_1206_ = lean_ctor_get(v_key_1191_, 1);
v___x_1207_ = lean_expr_eqv(v_fst_1203_, v_fst_1205_);
if (v___x_1207_ == 0)
{
v___y_1197_ = v___x_1207_;
goto v___jp_1196_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_nat_dec_eq(v_snd_1204_, v_snd_1206_);
v___y_1197_ = v___x_1208_;
goto v___jp_1196_;
}
v___jp_1196_:
{
if (v___y_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_del_object(v___x_1194_);
v___x_1198_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1191_, v_val_1192_, v_x_1169_, v_x_1170_);
v___x_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
v___y_1186_ = v___x_1199_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1201_; 
lean_dec(v_val_1192_);
lean_dec(v_key_1191_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v_x_1170_);
lean_ctor_set(v___x_1194_, 0, v_x_1169_);
v___x_1201_ = v___x_1194_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_x_1169_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_x_1170_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
v___y_1186_ = v___x_1201_;
goto v___jp_1185_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1220_; 
v_node_1210_ = lean_ctor_get(v_v_1182_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_v_1182_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1212_ = v_v_1182_;
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_node_1210_);
lean_dec(v_v_1182_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
size_t v___x_1214_; size_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1214_ = lean_usize_shift_right(v_x_1167_, v___x_1172_);
v___x_1215_ = lean_usize_add(v_x_1168_, v___x_1173_);
v___x_1216_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg(v_node_1210_, v___x_1214_, v___x_1215_, v_x_1169_, v_x_1170_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1216_);
v___x_1218_ = v___x_1212_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
v___y_1186_ = v___x_1218_;
goto v___jp_1185_;
}
}
}
default: 
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_x_1169_);
lean_ctor_set(v___x_1221_, 1, v_x_1170_);
v___y_1186_ = v___x_1221_;
goto v___jp_1185_;
}
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_array_fset(v_xs_x27_1184_, v_j_1176_, v___y_1186_);
lean_dec(v_j_1176_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1187_);
v___x_1189_ = v___x_1180_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
lean_object* v_ks_1224_; lean_object* v_vs_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1245_; 
v_ks_1224_ = lean_ctor_get(v_x_1166_, 0);
v_vs_1225_ = lean_ctor_get(v_x_1166_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_1166_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1227_ = v_x_1166_;
v_isShared_1228_ = v_isSharedCheck_1245_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_vs_1225_);
lean_inc(v_ks_1224_);
lean_dec(v_x_1166_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1245_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_ks_1224_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_vs_1225_);
v___x_1230_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v_newNode_1231_; uint8_t v___y_1233_; size_t v___x_1239_; uint8_t v___x_1240_; 
v_newNode_1231_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1___redArg(v___x_1230_, v_x_1169_, v_x_1170_);
v___x_1239_ = ((size_t)7ULL);
v___x_1240_ = lean_usize_dec_le(v___x_1239_, v_x_1168_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1241_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1231_);
v___x_1242_ = lean_unsigned_to_nat(4u);
v___x_1243_ = lean_nat_dec_lt(v___x_1241_, v___x_1242_);
lean_dec(v___x_1241_);
v___y_1233_ = v___x_1243_;
goto v___jp_1232_;
}
else
{
v___y_1233_ = v___x_1240_;
goto v___jp_1232_;
}
v___jp_1232_:
{
if (v___y_1233_ == 0)
{
lean_object* v_ks_1234_; lean_object* v_vs_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_ks_1234_ = lean_ctor_get(v_newNode_1231_, 0);
lean_inc_ref(v_ks_1234_);
v_vs_1235_ = lean_ctor_get(v_newNode_1231_, 1);
lean_inc_ref(v_vs_1235_);
lean_dec_ref(v_newNode_1231_);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___closed__0);
v___x_1238_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___redArg(v_x_1168_, v_ks_1234_, v_vs_1235_, v___x_1236_, v___x_1237_);
lean_dec_ref(v_vs_1235_);
lean_dec_ref(v_ks_1234_);
return v___x_1238_;
}
else
{
return v_newNode_1231_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___redArg(size_t v_depth_1246_, lean_object* v_keys_1247_, lean_object* v_vals_1248_, lean_object* v_i_1249_, lean_object* v_entries_1250_){
_start:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_array_get_size(v_keys_1247_);
v___x_1252_ = lean_nat_dec_lt(v_i_1249_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec(v_i_1249_);
return v_entries_1250_;
}
else
{
lean_object* v_k_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v_v_1256_; uint64_t v___x_1257_; uint64_t v___x_1258_; uint64_t v___x_1259_; size_t v_h_1260_; size_t v___x_1261_; lean_object* v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; size_t v_h_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_k_1253_ = lean_array_fget_borrowed(v_keys_1247_, v_i_1249_);
v_fst_1254_ = lean_ctor_get(v_k_1253_, 0);
v_snd_1255_ = lean_ctor_get(v_k_1253_, 1);
v_v_1256_ = lean_array_fget_borrowed(v_vals_1248_, v_i_1249_);
v___x_1257_ = l_Lean_Expr_hash(v_fst_1254_);
v___x_1258_ = lean_uint64_of_nat(v_snd_1255_);
v___x_1259_ = lean_uint64_mix_hash(v___x_1257_, v___x_1258_);
v_h_1260_ = lean_uint64_to_usize(v___x_1259_);
v___x_1261_ = ((size_t)5ULL);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_sub(v_depth_1246_, v___x_1263_);
v___x_1265_ = lean_usize_mul(v___x_1261_, v___x_1264_);
v_h_1266_ = lean_usize_shift_right(v_h_1260_, v___x_1265_);
v___x_1267_ = lean_nat_add(v_i_1249_, v___x_1262_);
lean_dec(v_i_1249_);
lean_inc(v_v_1256_);
lean_inc(v_k_1253_);
v___x_1268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg(v_entries_1250_, v_h_1266_, v_depth_1246_, v_k_1253_, v_v_1256_);
v_i_1249_ = v___x_1267_;
v_entries_1250_ = v___x_1268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1270_, lean_object* v_keys_1271_, lean_object* v_vals_1272_, lean_object* v_i_1273_, lean_object* v_entries_1274_){
_start:
{
size_t v_depth_boxed_1275_; lean_object* v_res_1276_; 
v_depth_boxed_1275_ = lean_unbox_usize(v_depth_1270_);
lean_dec(v_depth_1270_);
v_res_1276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1275_, v_keys_1271_, v_vals_1272_, v_i_1273_, v_entries_1274_);
lean_dec_ref(v_vals_1272_);
lean_dec_ref(v_keys_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg___boxed(lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
size_t v_x_28969__boxed_1282_; size_t v_x_28970__boxed_1283_; lean_object* v_res_1284_; 
v_x_28969__boxed_1282_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_x_28970__boxed_1283_ = lean_unbox_usize(v_x_1279_);
lean_dec(v_x_1279_);
v_res_1284_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg(v_x_1277_, v_x_28969__boxed_1282_, v_x_28970__boxed_1283_, v_x_1280_, v_x_1281_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0___redArg(lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v_fst_1288_; lean_object* v_snd_1289_; uint64_t v___x_1290_; uint64_t v___x_1291_; uint64_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v_fst_1288_ = lean_ctor_get(v_x_1286_, 0);
v_snd_1289_ = lean_ctor_get(v_x_1286_, 1);
v___x_1290_ = l_Lean_Expr_hash(v_fst_1288_);
v___x_1291_ = lean_uint64_of_nat(v_snd_1289_);
v___x_1292_ = lean_uint64_mix_hash(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_uint64_to_usize(v___x_1292_);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg(v_x_1285_, v___x_1293_, v___x_1294_, v_x_1286_, v_x_1287_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_1296_, lean_object* v_vals_1297_, lean_object* v_i_1298_, lean_object* v_k_1299_){
_start:
{
uint8_t v___y_1301_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_array_get_size(v_keys_1296_);
v___x_1308_ = lean_nat_dec_lt(v_i_1298_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec(v_i_1298_);
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
else
{
lean_object* v_fst_1310_; lean_object* v_snd_1311_; lean_object* v_k_x27_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; uint8_t v___x_1315_; 
v_fst_1310_ = lean_ctor_get(v_k_1299_, 0);
v_snd_1311_ = lean_ctor_get(v_k_1299_, 1);
v_k_x27_1312_ = lean_array_fget_borrowed(v_keys_1296_, v_i_1298_);
v_fst_1313_ = lean_ctor_get(v_k_x27_1312_, 0);
v_snd_1314_ = lean_ctor_get(v_k_x27_1312_, 1);
v___x_1315_ = lean_expr_eqv(v_fst_1310_, v_fst_1313_);
if (v___x_1315_ == 0)
{
v___y_1301_ = v___x_1315_;
goto v___jp_1300_;
}
else
{
uint8_t v___x_1316_; 
v___x_1316_ = lean_nat_dec_eq(v_snd_1311_, v_snd_1314_);
v___y_1301_ = v___x_1316_;
goto v___jp_1300_;
}
}
v___jp_1300_:
{
if (v___y_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_nat_add(v_i_1298_, v___x_1302_);
lean_dec(v_i_1298_);
v_i_1298_ = v___x_1303_;
goto _start;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_array_fget_borrowed(v_vals_1297_, v_i_1298_);
lean_dec(v_i_1298_);
lean_inc(v___x_1305_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_1317_, lean_object* v_vals_1318_, lean_object* v_i_1319_, lean_object* v_k_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___redArg(v_keys_1317_, v_vals_1318_, v_i_1319_, v_k_1320_);
lean_dec_ref(v_k_1320_);
lean_dec_ref(v_vals_1318_);
lean_dec_ref(v_keys_1317_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___redArg(lean_object* v_x_1322_, size_t v_x_1323_, lean_object* v_x_1324_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_object* v_es_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1353_; 
v_es_1325_ = lean_ctor_get(v_x_1322_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_x_1322_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1327_ = v_x_1322_;
v_isShared_1328_ = v_isSharedCheck_1353_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_es_1325_);
lean_dec(v_x_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1353_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; lean_object* v_j_1333_; lean_object* v___x_1334_; 
v___x_1329_ = lean_box(2);
v___x_1330_ = ((size_t)5ULL);
v___x_1331_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1);
v___x_1332_ = lean_usize_land(v_x_1323_, v___x_1331_);
v_j_1333_ = lean_usize_to_nat(v___x_1332_);
v___x_1334_ = lean_array_get(v___x_1329_, v_es_1325_, v_j_1333_);
lean_dec(v_j_1333_);
lean_dec_ref(v_es_1325_);
switch(lean_obj_tag(v___x_1334_))
{
case 0:
{
lean_object* v_key_1335_; lean_object* v_val_1336_; uint8_t v___y_1338_; lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; uint8_t v___x_1347_; 
v_key_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_key_1335_);
v_val_1336_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_val_1336_);
lean_dec_ref(v___x_1334_);
v_fst_1343_ = lean_ctor_get(v_x_1324_, 0);
v_snd_1344_ = lean_ctor_get(v_x_1324_, 1);
v_fst_1345_ = lean_ctor_get(v_key_1335_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v_key_1335_, 1);
lean_inc(v_snd_1346_);
lean_dec(v_key_1335_);
v___x_1347_ = lean_expr_eqv(v_fst_1343_, v_fst_1345_);
lean_dec(v_fst_1345_);
if (v___x_1347_ == 0)
{
lean_dec(v_snd_1346_);
v___y_1338_ = v___x_1347_;
goto v___jp_1337_;
}
else
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_nat_dec_eq(v_snd_1344_, v_snd_1346_);
lean_dec(v_snd_1346_);
v___y_1338_ = v___x_1348_;
goto v___jp_1337_;
}
v___jp_1337_:
{
if (v___y_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec(v_val_1336_);
lean_del_object(v___x_1327_);
v___x_1339_ = lean_box(0);
return v___x_1339_;
}
else
{
lean_object* v___x_1341_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
lean_ctor_set(v___x_1327_, 0, v_val_1336_);
v___x_1341_ = v___x_1327_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_val_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
case 1:
{
lean_object* v_node_1349_; size_t v___x_1350_; 
lean_del_object(v___x_1327_);
v_node_1349_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_node_1349_);
lean_dec_ref(v___x_1334_);
v___x_1350_ = lean_usize_shift_right(v_x_1323_, v___x_1330_);
v_x_1322_ = v_node_1349_;
v_x_1323_ = v___x_1350_;
goto _start;
}
default: 
{
lean_object* v___x_1352_; 
lean_del_object(v___x_1327_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_ks_1354_; lean_object* v_vs_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_ks_1354_ = lean_ctor_get(v_x_1322_, 0);
lean_inc_ref(v_ks_1354_);
v_vs_1355_ = lean_ctor_get(v_x_1322_, 1);
lean_inc_ref(v_vs_1355_);
lean_dec_ref(v_x_1322_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___redArg(v_ks_1354_, v_vs_1355_, v___x_1356_, v_x_1324_);
lean_dec_ref(v_vs_1355_);
lean_dec_ref(v_ks_1354_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___redArg___boxed(lean_object* v_x_1358_, lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
size_t v_x_29203__boxed_1361_; lean_object* v_res_1362_; 
v_x_29203__boxed_1361_ = lean_unbox_usize(v_x_1359_);
lean_dec(v_x_1359_);
v_res_1362_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___redArg(v_x_1358_, v_x_29203__boxed_1361_, v_x_1360_);
lean_dec_ref(v_x_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___redArg(lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v_fst_1365_; lean_object* v_snd_1366_; uint64_t v___x_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v_fst_1365_ = lean_ctor_get(v_x_1364_, 0);
v_snd_1366_ = lean_ctor_get(v_x_1364_, 1);
v___x_1367_ = l_Lean_Expr_hash(v_fst_1365_);
v___x_1368_ = lean_uint64_of_nat(v_snd_1366_);
v___x_1369_ = lean_uint64_mix_hash(v___x_1367_, v___x_1368_);
v___x_1370_ = lean_uint64_to_usize(v___x_1369_);
v___x_1371_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___redArg(v_x_1363_, v___x_1370_, v_x_1364_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___redArg___boxed(lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___redArg(v_x_1372_, v_x_1373_);
lean_dec_ref(v_x_1373_);
return v_res_1374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__1(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__0));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__3(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__2));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__5(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__4));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go(lean_object* v_parent_1384_, lean_object* v_f_1385_, lean_object* v_i_1386_, lean_object* v_e_1387_, uint8_t v_useIsDefEqBounded_1388_, uint8_t v_isInst_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1401_; 
lean_inc(v_a_1399_);
lean_inc_ref(v_a_1398_);
lean_inc(v_a_1397_);
lean_inc_ref(v_a_1396_);
lean_inc_ref(v_e_1387_);
v___x_1401_ = lean_infer_type(v_e_1387_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1594_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1594_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1594_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; 
if (v_isInst_1389_ == 0)
{
v___y_1549_ = v_a_1390_;
v___y_1550_ = v_a_1391_;
v___y_1551_ = v_a_1392_;
v___y_1552_ = v_a_1393_;
v___y_1553_ = v_a_1394_;
v___y_1554_ = v_a_1395_;
v___y_1555_ = v_a_1396_;
v___y_1556_ = v_a_1397_;
v___y_1557_ = v_a_1398_;
v___y_1558_ = v_a_1399_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Meta_Grind_getBuiltinInstance_x3f(v_a_1402_);
if (lean_obj_tag(v___x_1574_) == 1)
{
lean_object* v_val_1575_; lean_object* v___x_1576_; 
v_val_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1575_);
lean_dec_ref(v___x_1574_);
lean_inc(v_a_1399_);
lean_inc_ref(v_a_1398_);
lean_inc(v_a_1397_);
lean_inc_ref(v_a_1396_);
lean_inc(v_a_1395_);
lean_inc_ref(v_a_1394_);
lean_inc(v_a_1393_);
lean_inc_ref(v_a_1392_);
lean_inc(v_a_1391_);
lean_inc(v_a_1390_);
lean_inc(v_val_1575_);
lean_inc_ref(v_e_1387_);
lean_inc_ref(v_parent_1384_);
v___x_1576_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq(v_parent_1384_, v_useIsDefEqBounded_1388_, v_e_1387_, v_val_1575_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_unbox(v_a_1577_);
lean_dec(v_a_1577_);
if (v___x_1581_ == 0)
{
lean_del_object(v___x_1579_);
lean_dec(v_val_1575_);
v___y_1549_ = v_a_1390_;
v___y_1550_ = v_a_1391_;
v___y_1551_ = v_a_1392_;
v___y_1552_ = v_a_1393_;
v___y_1553_ = v_a_1394_;
v___y_1554_ = v_a_1395_;
v___y_1555_ = v_a_1396_;
v___y_1556_ = v_a_1397_;
v___y_1557_ = v_a_1398_;
v___y_1558_ = v_a_1399_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1583_; 
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_e_1387_);
lean_dec(v_i_1386_);
lean_dec_ref(v_f_1385_);
lean_dec_ref(v_parent_1384_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_val_1575_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_val_1575_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec(v_val_1575_);
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_e_1387_);
lean_dec(v_i_1386_);
lean_dec_ref(v_f_1385_);
lean_dec_ref(v_parent_1384_);
v_a_1586_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1576_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1576_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_dec(v___x_1574_);
v___y_1549_ = v_a_1390_;
v___y_1550_ = v_a_1391_;
v___y_1551_ = v_a_1392_;
v___y_1552_ = v_a_1393_;
v___y_1553_ = v_a_1394_;
v___y_1554_ = v_a_1395_;
v___y_1555_ = v_a_1396_;
v___y_1556_ = v_a_1397_;
v___y_1557_ = v_a_1398_;
v___y_1558_ = v_a_1399_;
goto v___jp_1548_;
}
}
v___jp_1406_:
{
lean_object* v___x_1410_; lean_object* v_toGoalState_1411_; lean_object* v_canon_1412_; lean_object* v_mvarId_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1465_; 
v___x_1410_ = lean_st_ref_take(v___y_1409_);
v_toGoalState_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_ref(v_toGoalState_1411_);
v_canon_1412_ = lean_ctor_get(v_toGoalState_1411_, 1);
lean_inc_ref(v_canon_1412_);
v_mvarId_1413_ = lean_ctor_get(v___x_1410_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1466_);
v___x_1415_ = v___x_1410_;
v_isShared_1416_ = v_isSharedCheck_1465_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_mvarId_1413_);
lean_dec(v___x_1410_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1465_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_nextDeclIdx_1417_; lean_object* v_enodeMap_1418_; lean_object* v_exprs_1419_; lean_object* v_parents_1420_; lean_object* v_congrTable_1421_; lean_object* v_appMap_1422_; lean_object* v_indicesFound_1423_; lean_object* v_newFacts_1424_; uint8_t v_inconsistent_1425_; lean_object* v_nextIdx_1426_; lean_object* v_newRawFacts_1427_; lean_object* v_facts_1428_; lean_object* v_extThms_1429_; lean_object* v_ematch_1430_; lean_object* v_inj_1431_; lean_object* v_split_1432_; lean_object* v_clean_1433_; lean_object* v_sstates_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1463_; 
v_nextDeclIdx_1417_ = lean_ctor_get(v_toGoalState_1411_, 0);
v_enodeMap_1418_ = lean_ctor_get(v_toGoalState_1411_, 2);
v_exprs_1419_ = lean_ctor_get(v_toGoalState_1411_, 3);
v_parents_1420_ = lean_ctor_get(v_toGoalState_1411_, 4);
v_congrTable_1421_ = lean_ctor_get(v_toGoalState_1411_, 5);
v_appMap_1422_ = lean_ctor_get(v_toGoalState_1411_, 6);
v_indicesFound_1423_ = lean_ctor_get(v_toGoalState_1411_, 7);
v_newFacts_1424_ = lean_ctor_get(v_toGoalState_1411_, 8);
v_inconsistent_1425_ = lean_ctor_get_uint8(v_toGoalState_1411_, sizeof(void*)*18);
v_nextIdx_1426_ = lean_ctor_get(v_toGoalState_1411_, 9);
v_newRawFacts_1427_ = lean_ctor_get(v_toGoalState_1411_, 10);
v_facts_1428_ = lean_ctor_get(v_toGoalState_1411_, 11);
v_extThms_1429_ = lean_ctor_get(v_toGoalState_1411_, 12);
v_ematch_1430_ = lean_ctor_get(v_toGoalState_1411_, 13);
v_inj_1431_ = lean_ctor_get(v_toGoalState_1411_, 14);
v_split_1432_ = lean_ctor_get(v_toGoalState_1411_, 15);
v_clean_1433_ = lean_ctor_get(v_toGoalState_1411_, 16);
v_sstates_1434_ = lean_ctor_get(v_toGoalState_1411_, 17);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_toGoalState_1411_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_toGoalState_1411_, 1);
lean_dec(v_unused_1464_);
v___x_1436_ = v_toGoalState_1411_;
v_isShared_1437_ = v_isSharedCheck_1463_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_sstates_1434_);
lean_inc(v_clean_1433_);
lean_inc(v_split_1432_);
lean_inc(v_inj_1431_);
lean_inc(v_ematch_1430_);
lean_inc(v_extThms_1429_);
lean_inc(v_facts_1428_);
lean_inc(v_newRawFacts_1427_);
lean_inc(v_nextIdx_1426_);
lean_inc(v_newFacts_1424_);
lean_inc(v_indicesFound_1423_);
lean_inc(v_appMap_1422_);
lean_inc(v_congrTable_1421_);
lean_inc(v_parents_1420_);
lean_inc(v_exprs_1419_);
lean_inc(v_enodeMap_1418_);
lean_inc(v_nextDeclIdx_1417_);
lean_dec(v_toGoalState_1411_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1463_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_argMap_1438_; lean_object* v_canon_1439_; lean_object* v_proofCanon_1440_; lean_object* v_canonArg_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1462_; 
v_argMap_1438_ = lean_ctor_get(v_canon_1412_, 0);
v_canon_1439_ = lean_ctor_get(v_canon_1412_, 1);
v_proofCanon_1440_ = lean_ctor_get(v_canon_1412_, 2);
v_canonArg_1441_ = lean_ctor_get(v_canon_1412_, 3);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_canon_1412_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1443_ = v_canon_1412_;
v_isShared_1444_ = v_isSharedCheck_1462_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_canonArg_1441_);
lean_inc(v_proofCanon_1440_);
lean_inc(v_canon_1439_);
lean_inc(v_argMap_1438_);
lean_dec(v_canon_1412_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1462_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_inc_ref(v_e_1387_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_e_1387_);
lean_ctor_set(v___x_1445_, 1, v_a_1402_);
v___x_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___y_1407_);
v___x_1447_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0___redArg(v_argMap_1438_, v___y_1408_, v___x_1446_);
lean_inc_ref_n(v_e_1387_, 2);
v___x_1448_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0___redArg(v_canon_1439_, v_e_1387_, v_e_1387_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1448_);
lean_ctor_set(v___x_1443_, 0, v___x_1447_);
v___x_1450_ = v___x_1443_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_proofCanon_1440_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_canonArg_1441_);
v___x_1450_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1450_);
v___x_1452_ = v___x_1436_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_nextDeclIdx_1417_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_enodeMap_1418_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_exprs_1419_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_parents_1420_);
lean_ctor_set(v_reuseFailAlloc_1460_, 5, v_congrTable_1421_);
lean_ctor_set(v_reuseFailAlloc_1460_, 6, v_appMap_1422_);
lean_ctor_set(v_reuseFailAlloc_1460_, 7, v_indicesFound_1423_);
lean_ctor_set(v_reuseFailAlloc_1460_, 8, v_newFacts_1424_);
lean_ctor_set(v_reuseFailAlloc_1460_, 9, v_nextIdx_1426_);
lean_ctor_set(v_reuseFailAlloc_1460_, 10, v_newRawFacts_1427_);
lean_ctor_set(v_reuseFailAlloc_1460_, 11, v_facts_1428_);
lean_ctor_set(v_reuseFailAlloc_1460_, 12, v_extThms_1429_);
lean_ctor_set(v_reuseFailAlloc_1460_, 13, v_ematch_1430_);
lean_ctor_set(v_reuseFailAlloc_1460_, 14, v_inj_1431_);
lean_ctor_set(v_reuseFailAlloc_1460_, 15, v_split_1432_);
lean_ctor_set(v_reuseFailAlloc_1460_, 16, v_clean_1433_);
lean_ctor_set(v_reuseFailAlloc_1460_, 17, v_sstates_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, sizeof(void*)*18, v_inconsistent_1425_);
v___x_1452_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1452_);
v___x_1454_ = v___x_1415_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_mvarId_1413_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_st_ref_set(v___y_1409_, v___x_1454_);
lean_dec(v___y_1409_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_e_1387_);
v___x_1457_ = v___x_1404_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_e_1387_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
}
}
v___jp_1467_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg___closed__0));
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1476_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1473_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1469_);
lean_inc(v___y_1470_);
lean_inc(v___y_1479_);
lean_inc_ref(v_e_1387_);
lean_inc(v_a_1402_);
v___x_1481_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg(v_a_1402_, v_parent_1384_, v_useIsDefEqBounded_1388_, v_e_1387_, v___y_1479_, v___x_1480_, v___y_1470_, v___y_1469_, v___y_1478_, v___y_1474_, v___y_1473_, v___y_1472_, v___y_1477_, v___y_1476_, v___y_1468_, v___y_1471_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1539_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1539_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1539_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_fst_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1537_; 
v_fst_1486_ = lean_ctor_get(v_a_1482_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_a_1482_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_a_1482_, 1);
lean_dec(v_unused_1538_);
v___x_1488_ = v_a_1482_;
v_isShared_1489_ = v_isSharedCheck_1537_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_fst_1486_);
lean_dec(v_a_1482_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1537_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
if (lean_obj_tag(v_fst_1486_) == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1532_; 
lean_del_object(v___x_1484_);
v___x_1490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3));
v___x_1491_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(v___x_1490_, v___y_1468_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1532_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1532_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_unbox(v_a_1492_);
lean_dec(v_a_1492_);
if (v___x_1496_ == 0)
{
lean_del_object(v___x_1494_);
lean_del_object(v___x_1488_);
lean_dec_ref(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_i_1386_);
lean_dec_ref(v_f_1385_);
v___y_1407_ = v___y_1479_;
v___y_1408_ = v___y_1475_;
v___y_1409_ = v___y_1470_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_Meta_Grind_updateLastTag(v___y_1470_, v___y_1469_, v___y_1478_, v___y_1474_, v___y_1473_, v___y_1472_, v___y_1477_, v___y_1476_, v___y_1468_, v___y_1471_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1469_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_dec_ref(v___x_1497_);
v___x_1498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__1);
v___x_1499_ = l_Lean_MessageData_ofExpr(v_f_1385_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 7);
lean_ctor_set(v___x_1488_, 1, v___x_1499_);
lean_ctor_set(v___x_1488_, 0, v___x_1498_);
v___x_1501_ = v___x_1488_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__3);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = l_Nat_reprFast(v_i_1386_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 3);
lean_ctor_set(v___x_1494_, 0, v___x_1504_);
v___x_1506_ = v___x_1494_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1507_ = l_Lean_MessageData_ofFormat(v___x_1506_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1503_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___closed__5);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
lean_inc_ref(v_e_1387_);
v___x_1511_ = l_Lean_MessageData_ofExpr(v_e_1387_);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(v___x_1490_, v___x_1512_, v___y_1477_, v___y_1476_, v___y_1468_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1477_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_dec_ref(v___x_1513_);
v___y_1407_ = v___y_1479_;
v___y_1408_ = v___y_1475_;
v___y_1409_ = v___y_1470_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1470_);
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_dec_ref(v_e_1387_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_del_object(v___x_1494_);
lean_del_object(v___x_1488_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1468_);
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_dec_ref(v_e_1387_);
lean_dec(v_i_1386_);
lean_dec_ref(v_f_1385_);
v_a_1524_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1497_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1497_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1535_; 
lean_del_object(v___x_1488_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_dec_ref(v_e_1387_);
lean_dec(v_i_1386_);
lean_dec_ref(v_f_1385_);
v_val_1533_ = lean_ctor_get(v_fst_1486_, 0);
lean_inc(v_val_1533_);
lean_dec_ref(v_fst_1486_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v_val_1533_);
v___x_1535_ = v___x_1484_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_val_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_dec_ref(v_e_1387_);
lean_dec(v_i_1386_);
lean_dec_ref(v_f_1385_);
v_a_1540_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1481_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1481_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
v___jp_1548_:
{
lean_object* v___x_1559_; lean_object* v_toGoalState_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1572_; 
v___x_1559_ = lean_st_ref_get(v___y_1549_);
v_toGoalState_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v___x_1559_, 1);
lean_dec(v_unused_1573_);
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_toGoalState_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_canon_1564_; lean_object* v_argMap_1565_; lean_object* v___x_1567_; 
v_canon_1564_ = lean_ctor_get(v_toGoalState_1560_, 1);
lean_inc_ref(v_canon_1564_);
lean_dec_ref(v_toGoalState_1560_);
v_argMap_1565_ = lean_ctor_get(v_canon_1564_, 0);
lean_inc_ref(v_argMap_1565_);
lean_dec_ref(v_canon_1564_);
lean_inc(v_i_1386_);
lean_inc_ref(v_f_1385_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v_i_1386_);
lean_ctor_set(v___x_1562_, 0, v_f_1385_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_f_1385_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_i_1386_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___redArg(v_argMap_1565_, v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_box(0);
v___y_1468_ = v___y_1557_;
v___y_1469_ = v___y_1550_;
v___y_1470_ = v___y_1549_;
v___y_1471_ = v___y_1558_;
v___y_1472_ = v___y_1554_;
v___y_1473_ = v___y_1553_;
v___y_1474_ = v___y_1552_;
v___y_1475_ = v___x_1567_;
v___y_1476_ = v___y_1556_;
v___y_1477_ = v___y_1555_;
v___y_1478_ = v___y_1551_;
v___y_1479_ = v___x_1569_;
goto v___jp_1467_;
}
else
{
lean_object* v_val_1570_; 
v_val_1570_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_val_1570_);
lean_dec_ref(v___x_1568_);
v___y_1468_ = v___y_1557_;
v___y_1469_ = v___y_1550_;
v___y_1470_ = v___y_1549_;
v___y_1471_ = v___y_1558_;
v___y_1472_ = v___y_1554_;
v___y_1473_ = v___y_1553_;
v___y_1474_ = v___y_1552_;
v___y_1475_ = v___x_1567_;
v___y_1476_ = v___y_1556_;
v___y_1477_ = v___y_1555_;
v___y_1478_ = v___y_1551_;
v___y_1479_ = v_val_1570_;
goto v___jp_1467_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_e_1387_);
lean_dec(v_i_1386_);
lean_dec_ref(v_f_1385_);
lean_dec_ref(v_parent_1384_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go___boxed(lean_object** _args){
lean_object* v_parent_1595_ = _args[0];
lean_object* v_f_1596_ = _args[1];
lean_object* v_i_1597_ = _args[2];
lean_object* v_e_1598_ = _args[3];
lean_object* v_useIsDefEqBounded_1599_ = _args[4];
lean_object* v_isInst_1600_ = _args[5];
lean_object* v_a_1601_ = _args[6];
lean_object* v_a_1602_ = _args[7];
lean_object* v_a_1603_ = _args[8];
lean_object* v_a_1604_ = _args[9];
lean_object* v_a_1605_ = _args[10];
lean_object* v_a_1606_ = _args[11];
lean_object* v_a_1607_ = _args[12];
lean_object* v_a_1608_ = _args[13];
lean_object* v_a_1609_ = _args[14];
lean_object* v_a_1610_ = _args[15];
lean_object* v_a_1611_ = _args[16];
_start:
{
uint8_t v_useIsDefEqBounded_boxed_1612_; uint8_t v_isInst_boxed_1613_; lean_object* v_res_1614_; 
v_useIsDefEqBounded_boxed_1612_ = lean_unbox(v_useIsDefEqBounded_1599_);
v_isInst_boxed_1613_ = lean_unbox(v_isInst_1600_);
v_res_1614_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go(v_parent_1595_, v_f_1596_, v_i_1597_, v_e_1598_, v_useIsDefEqBounded_boxed_1612_, v_isInst_boxed_1613_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0(lean_object* v_00_u03b2_1615_, lean_object* v_x_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0___redArg(v_x_1616_, v_x_1617_, v_x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1(lean_object* v_a_1620_, lean_object* v_parent_1621_, uint8_t v_useIsDefEqBounded_1622_, lean_object* v_e_1623_, lean_object* v_as_1624_, lean_object* v_as_x27_1625_, lean_object* v_b_1626_, lean_object* v_a_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___redArg(v_a_1620_, v_parent_1621_, v_useIsDefEqBounded_1622_, v_e_1623_, v_as_x27_1625_, v_b_1626_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1___boxed(lean_object** _args){
lean_object* v_a_1640_ = _args[0];
lean_object* v_parent_1641_ = _args[1];
lean_object* v_useIsDefEqBounded_1642_ = _args[2];
lean_object* v_e_1643_ = _args[3];
lean_object* v_as_1644_ = _args[4];
lean_object* v_as_x27_1645_ = _args[5];
lean_object* v_b_1646_ = _args[6];
lean_object* v_a_1647_ = _args[7];
lean_object* v___y_1648_ = _args[8];
lean_object* v___y_1649_ = _args[9];
lean_object* v___y_1650_ = _args[10];
lean_object* v___y_1651_ = _args[11];
lean_object* v___y_1652_ = _args[12];
lean_object* v___y_1653_ = _args[13];
lean_object* v___y_1654_ = _args[14];
lean_object* v___y_1655_ = _args[15];
lean_object* v___y_1656_ = _args[16];
lean_object* v___y_1657_ = _args[17];
lean_object* v___y_1658_ = _args[18];
_start:
{
uint8_t v_useIsDefEqBounded_boxed_1659_; lean_object* v_res_1660_; 
v_useIsDefEqBounded_boxed_1659_ = lean_unbox(v_useIsDefEqBounded_1642_);
v_res_1660_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__1(v_a_1640_, v_parent_1641_, v_useIsDefEqBounded_boxed_1659_, v_e_1643_, v_as_1644_, v_as_x27_1645_, v_b_1646_, v_a_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v_as_1644_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2(lean_object* v_00_u03b2_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___redArg(v_x_1662_, v_x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2(v_00_u03b2_1665_, v_x_1666_, v_x_1667_);
lean_dec_ref(v_x_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0(lean_object* v_00_u03b2_1669_, lean_object* v_x_1670_, size_t v_x_1671_, size_t v_x_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___redArg(v_x_1670_, v_x_1671_, v_x_1672_, v_x_1673_, v_x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
size_t v_x_29759__boxed_1682_; size_t v_x_29760__boxed_1683_; lean_object* v_res_1684_; 
v_x_29759__boxed_1682_ = lean_unbox_usize(v_x_1678_);
lean_dec(v_x_1678_);
v_x_29760__boxed_1683_ = lean_unbox_usize(v_x_1679_);
lean_dec(v_x_1679_);
v_res_1684_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0(v_00_u03b2_1676_, v_x_1677_, v_x_29759__boxed_1682_, v_x_29760__boxed_1683_, v_x_1680_, v_x_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3(lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, size_t v_x_1687_, lean_object* v_x_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___redArg(v_x_1686_, v_x_1687_, v_x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_, lean_object* v_x_1693_){
_start:
{
size_t v_x_29776__boxed_1694_; lean_object* v_res_1695_; 
v_x_29776__boxed_1694_ = lean_unbox_usize(v_x_1692_);
lean_dec(v_x_1692_);
v_res_1695_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3(v_00_u03b2_1690_, v_x_1691_, v_x_29776__boxed_1694_, v_x_1693_);
lean_dec_ref(v_x_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1696_, lean_object* v_n_1697_, lean_object* v_k_1698_, lean_object* v_v_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1___redArg(v_n_1697_, v_k_1698_, v_v_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1701_, size_t v_depth_1702_, lean_object* v_keys_1703_, lean_object* v_vals_1704_, lean_object* v_heq_1705_, lean_object* v_i_1706_, lean_object* v_entries_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___redArg(v_depth_1702_, v_keys_1703_, v_vals_1704_, v_i_1706_, v_entries_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1709_, lean_object* v_depth_1710_, lean_object* v_keys_1711_, lean_object* v_vals_1712_, lean_object* v_heq_1713_, lean_object* v_i_1714_, lean_object* v_entries_1715_){
_start:
{
size_t v_depth_boxed_1716_; lean_object* v_res_1717_; 
v_depth_boxed_1716_ = lean_unbox_usize(v_depth_1710_);
lean_dec(v_depth_1710_);
v_res_1717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__2(v_00_u03b2_1709_, v_depth_boxed_1716_, v_keys_1711_, v_vals_1712_, v_heq_1713_, v_i_1714_, v_entries_1715_);
lean_dec_ref(v_vals_1712_);
lean_dec_ref(v_keys_1711_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1718_, lean_object* v_keys_1719_, lean_object* v_vals_1720_, lean_object* v_heq_1721_, lean_object* v_i_1722_, lean_object* v_k_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___redArg(v_keys_1719_, v_vals_1720_, v_i_1722_, v_k_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1725_, lean_object* v_keys_1726_, lean_object* v_vals_1727_, lean_object* v_heq_1728_, lean_object* v_i_1729_, lean_object* v_k_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__2_spec__3_spec__6(v_00_u03b2_1725_, v_keys_1726_, v_vals_1727_, v_heq_1728_, v_i_1729_, v_k_1730_);
lean_dec_ref(v_k_1730_);
lean_dec_ref(v_vals_1727_);
lean_dec_ref(v_keys_1726_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1733_, v_x_1734_, v_x_1735_, v_x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v_ks_1742_; lean_object* v_vs_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1767_; 
v_ks_1742_ = lean_ctor_get(v_x_1738_, 0);
v_vs_1743_ = lean_ctor_get(v_x_1738_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_x_1738_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1745_ = v_x_1738_;
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_vs_1743_);
lean_inc(v_ks_1742_);
lean_dec(v_x_1738_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1767_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = lean_array_get_size(v_ks_1742_);
v___x_1748_ = lean_nat_dec_lt(v_x_1739_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec(v_x_1739_);
v___x_1749_ = lean_array_push(v_ks_1742_, v_x_1740_);
v___x_1750_ = lean_array_push(v_vs_1743_, v_x_1741_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v___x_1750_);
lean_ctor_set(v___x_1745_, 0, v___x_1749_);
v___x_1752_ = v___x_1745_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
else
{
lean_object* v_k_x27_1754_; uint8_t v___x_1755_; 
v_k_x27_1754_ = lean_array_fget_borrowed(v_ks_1742_, v_x_1739_);
v___x_1755_ = l_Lean_Meta_Grind_instBEqCanonArgKey_beq(v_x_1740_, v_k_x27_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1757_; 
if (v_isShared_1746_ == 0)
{
v___x_1757_ = v___x_1745_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_ks_1742_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_vs_1743_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_nat_add(v_x_1739_, v___x_1758_);
lean_dec(v_x_1739_);
v_x_1738_ = v___x_1757_;
v_x_1739_ = v___x_1759_;
goto _start;
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1762_ = lean_array_fset(v_ks_1742_, v_x_1739_, v_x_1740_);
v___x_1763_ = lean_array_fset(v_vs_1743_, v_x_1739_, v_x_1741_);
lean_dec(v_x_1739_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v___x_1763_);
lean_ctor_set(v___x_1745_, 0, v___x_1762_);
v___x_1765_ = v___x_1745_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1768_, lean_object* v_k_1769_, lean_object* v_v_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1768_, v___x_1771_, v_k_1769_, v_v_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg(lean_object* v_x_1774_, size_t v_x_1775_, size_t v_x_1776_, lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
lean_object* v_es_1779_; size_t v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; lean_object* v_j_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_es_1779_ = lean_ctor_get(v_x_1774_, 0);
v___x_1780_ = ((size_t)5ULL);
v___x_1781_ = ((size_t)1ULL);
v___x_1782_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1);
v___x_1783_ = lean_usize_land(v_x_1775_, v___x_1782_);
v_j_1784_ = lean_usize_to_nat(v___x_1783_);
v___x_1785_ = lean_array_get_size(v_es_1779_);
v___x_1786_ = lean_nat_dec_lt(v_j_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec(v_j_1784_);
lean_dec(v_x_1778_);
lean_dec_ref(v_x_1777_);
return v_x_1774_;
}
else
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1823_; 
lean_inc_ref(v_es_1779_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1774_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_x_1774_, 0);
lean_dec(v_unused_1824_);
v___x_1788_ = v_x_1774_;
v_isShared_1789_ = v_isSharedCheck_1823_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_x_1774_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1823_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_v_1790_; lean_object* v___x_1791_; lean_object* v_xs_x27_1792_; lean_object* v___y_1794_; 
v_v_1790_ = lean_array_fget(v_es_1779_, v_j_1784_);
v___x_1791_ = lean_box(0);
v_xs_x27_1792_ = lean_array_fset(v_es_1779_, v_j_1784_, v___x_1791_);
switch(lean_obj_tag(v_v_1790_))
{
case 0:
{
lean_object* v_key_1799_; lean_object* v_val_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1810_; 
v_key_1799_ = lean_ctor_get(v_v_1790_, 0);
v_val_1800_ = lean_ctor_get(v_v_1790_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_v_1790_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1802_ = v_v_1790_;
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_val_1800_);
lean_inc(v_key_1799_);
lean_dec(v_v_1790_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
uint8_t v___x_1804_; 
v___x_1804_ = l_Lean_Meta_Grind_instBEqCanonArgKey_beq(v_x_1777_, v_key_1799_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_del_object(v___x_1802_);
v___x_1805_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1799_, v_val_1800_, v_x_1777_, v_x_1778_);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___y_1794_ = v___x_1806_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1808_; 
lean_dec(v_val_1800_);
lean_dec(v_key_1799_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v_x_1778_);
lean_ctor_set(v___x_1802_, 0, v_x_1777_);
v___x_1808_ = v___x_1802_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_x_1777_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_x_1778_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
v___y_1794_ = v___x_1808_;
goto v___jp_1793_;
}
}
}
}
case 1:
{
lean_object* v_node_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1821_; 
v_node_1811_ = lean_ctor_get(v_v_1790_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_v_1790_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1813_ = v_v_1790_;
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_node_1811_);
lean_dec(v_v_1790_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1815_ = lean_usize_shift_right(v_x_1775_, v___x_1780_);
v___x_1816_ = lean_usize_add(v_x_1776_, v___x_1781_);
v___x_1817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg(v_node_1811_, v___x_1815_, v___x_1816_, v_x_1777_, v_x_1778_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1817_);
v___x_1819_ = v___x_1813_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
v___y_1794_ = v___x_1819_;
goto v___jp_1793_;
}
}
}
default: 
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v_x_1777_);
lean_ctor_set(v___x_1822_, 1, v_x_1778_);
v___y_1794_ = v___x_1822_;
goto v___jp_1793_;
}
}
v___jp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = lean_array_fset(v_xs_x27_1792_, v_j_1784_, v___y_1794_);
lean_dec(v_j_1784_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1795_);
v___x_1797_ = v___x_1788_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
else
{
lean_object* v_ks_1825_; lean_object* v_vs_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1846_; 
v_ks_1825_ = lean_ctor_get(v_x_1774_, 0);
v_vs_1826_ = lean_ctor_get(v_x_1774_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_x_1774_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1828_ = v_x_1774_;
v_isShared_1829_ = v_isSharedCheck_1846_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_vs_1826_);
lean_inc(v_ks_1825_);
lean_dec(v_x_1774_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1846_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_ks_1825_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_vs_1826_);
v___x_1831_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v_newNode_1832_; uint8_t v___y_1834_; size_t v___x_1840_; uint8_t v___x_1841_; 
v_newNode_1832_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4___redArg(v___x_1831_, v_x_1777_, v_x_1778_);
v___x_1840_ = ((size_t)7ULL);
v___x_1841_ = lean_usize_dec_le(v___x_1840_, v_x_1776_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1832_);
v___x_1843_ = lean_unsigned_to_nat(4u);
v___x_1844_ = lean_nat_dec_lt(v___x_1842_, v___x_1843_);
lean_dec(v___x_1842_);
v___y_1834_ = v___x_1844_;
goto v___jp_1833_;
}
else
{
v___y_1834_ = v___x_1841_;
goto v___jp_1833_;
}
v___jp_1833_:
{
if (v___y_1834_ == 0)
{
lean_object* v_ks_1835_; lean_object* v_vs_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_ks_1835_ = lean_ctor_get(v_newNode_1832_, 0);
lean_inc_ref(v_ks_1835_);
v_vs_1836_ = lean_ctor_get(v_newNode_1832_, 1);
lean_inc_ref(v_vs_1836_);
lean_dec_ref(v_newNode_1832_);
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___closed__0);
v___x_1839_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___redArg(v_x_1776_, v_ks_1835_, v_vs_1836_, v___x_1837_, v___x_1838_);
lean_dec_ref(v_vs_1836_);
lean_dec_ref(v_ks_1835_);
return v___x_1839_;
}
else
{
return v_newNode_1832_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___redArg(size_t v_depth_1847_, lean_object* v_keys_1848_, lean_object* v_vals_1849_, lean_object* v_i_1850_, lean_object* v_entries_1851_){
_start:
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = lean_array_get_size(v_keys_1848_);
v___x_1853_ = lean_nat_dec_lt(v_i_1850_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec(v_i_1850_);
return v_entries_1851_;
}
else
{
lean_object* v_k_1854_; lean_object* v_v_1855_; uint64_t v___x_1856_; size_t v_h_1857_; size_t v___x_1858_; lean_object* v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; size_t v_h_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_k_1854_ = lean_array_fget_borrowed(v_keys_1848_, v_i_1850_);
v_v_1855_ = lean_array_fget_borrowed(v_vals_1849_, v_i_1850_);
v___x_1856_ = l_Lean_Meta_Grind_instHashableCanonArgKey_hash(v_k_1854_);
v_h_1857_ = lean_uint64_to_usize(v___x_1856_);
v___x_1858_ = ((size_t)5ULL);
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_sub(v_depth_1847_, v___x_1860_);
v___x_1862_ = lean_usize_mul(v___x_1858_, v___x_1861_);
v_h_1863_ = lean_usize_shift_right(v_h_1857_, v___x_1862_);
v___x_1864_ = lean_nat_add(v_i_1850_, v___x_1859_);
lean_dec(v_i_1850_);
lean_inc(v_v_1855_);
lean_inc(v_k_1854_);
v___x_1865_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg(v_entries_1851_, v_h_1863_, v_depth_1847_, v_k_1854_, v_v_1855_);
v_i_1850_ = v___x_1864_;
v_entries_1851_ = v___x_1865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1867_, lean_object* v_keys_1868_, lean_object* v_vals_1869_, lean_object* v_i_1870_, lean_object* v_entries_1871_){
_start:
{
size_t v_depth_boxed_1872_; lean_object* v_res_1873_; 
v_depth_boxed_1872_ = lean_unbox_usize(v_depth_1867_);
lean_dec(v_depth_1867_);
v_res_1873_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1872_, v_keys_1868_, v_vals_1869_, v_i_1870_, v_entries_1871_);
lean_dec_ref(v_vals_1869_);
lean_dec_ref(v_keys_1868_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
size_t v_x_4683__boxed_1879_; size_t v_x_4684__boxed_1880_; lean_object* v_res_1881_; 
v_x_4683__boxed_1879_ = lean_unbox_usize(v_x_1875_);
lean_dec(v_x_1875_);
v_x_4684__boxed_1880_ = lean_unbox_usize(v_x_1876_);
lean_dec(v_x_1876_);
v_res_1881_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg(v_x_1874_, v_x_4683__boxed_1879_, v_x_4684__boxed_1880_, v_x_1877_, v_x_1878_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
uint64_t v___x_1885_; size_t v___x_1886_; size_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = l_Lean_Meta_Grind_instHashableCanonArgKey_hash(v_x_1883_);
v___x_1886_ = lean_uint64_to_usize(v___x_1885_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg(v_x_1882_, v___x_1886_, v___x_1887_, v_x_1883_, v_x_1884_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1889_, lean_object* v_vals_1890_, lean_object* v_i_1891_, lean_object* v_k_1892_){
_start:
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = lean_array_get_size(v_keys_1889_);
v___x_1894_ = lean_nat_dec_lt(v_i_1891_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec(v_i_1891_);
v___x_1895_ = lean_box(0);
return v___x_1895_;
}
else
{
lean_object* v_k_x27_1896_; uint8_t v___x_1897_; 
v_k_x27_1896_ = lean_array_fget_borrowed(v_keys_1889_, v_i_1891_);
v___x_1897_ = l_Lean_Meta_Grind_instBEqCanonArgKey_beq(v_k_1892_, v_k_x27_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = lean_nat_add(v_i_1891_, v___x_1898_);
lean_dec(v_i_1891_);
v_i_1891_ = v___x_1899_;
goto _start;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_array_fget_borrowed(v_vals_1890_, v_i_1891_);
lean_dec(v_i_1891_);
lean_inc(v___x_1901_);
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1903_, lean_object* v_vals_1904_, lean_object* v_i_1905_, lean_object* v_k_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___redArg(v_keys_1903_, v_vals_1904_, v_i_1905_, v_k_1906_);
lean_dec_ref(v_k_1906_);
lean_dec_ref(v_vals_1904_);
lean_dec_ref(v_keys_1903_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___redArg(lean_object* v_x_1908_, size_t v_x_1909_, lean_object* v_x_1910_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_object* v_es_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1932_; 
v_es_1911_ = lean_ctor_get(v_x_1908_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1913_ = v_x_1908_;
v_isShared_1914_ = v_isSharedCheck_1932_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_es_1911_);
lean_dec(v_x_1908_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1932_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; size_t v___x_1916_; size_t v___x_1917_; size_t v___x_1918_; lean_object* v_j_1919_; lean_object* v___x_1920_; 
v___x_1915_ = lean_box(2);
v___x_1916_ = ((size_t)5ULL);
v___x_1917_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1);
v___x_1918_ = lean_usize_land(v_x_1909_, v___x_1917_);
v_j_1919_ = lean_usize_to_nat(v___x_1918_);
v___x_1920_ = lean_array_get(v___x_1915_, v_es_1911_, v_j_1919_);
lean_dec(v_j_1919_);
lean_dec_ref(v_es_1911_);
switch(lean_obj_tag(v___x_1920_))
{
case 0:
{
lean_object* v_key_1921_; lean_object* v_val_1922_; uint8_t v___x_1923_; 
v_key_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_key_1921_);
v_val_1922_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_val_1922_);
lean_dec_ref(v___x_1920_);
v___x_1923_ = l_Lean_Meta_Grind_instBEqCanonArgKey_beq(v_x_1910_, v_key_1921_);
lean_dec(v_key_1921_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec(v_val_1922_);
lean_del_object(v___x_1913_);
v___x_1924_ = lean_box(0);
return v___x_1924_;
}
else
{
lean_object* v___x_1926_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 1);
lean_ctor_set(v___x_1913_, 0, v_val_1922_);
v___x_1926_ = v___x_1913_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_val_1922_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
case 1:
{
lean_object* v_node_1928_; size_t v___x_1929_; 
lean_del_object(v___x_1913_);
v_node_1928_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_node_1928_);
lean_dec_ref(v___x_1920_);
v___x_1929_ = lean_usize_shift_right(v_x_1909_, v___x_1916_);
v_x_1908_ = v_node_1928_;
v_x_1909_ = v___x_1929_;
goto _start;
}
default: 
{
lean_object* v___x_1931_; 
lean_del_object(v___x_1913_);
v___x_1931_ = lean_box(0);
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_ks_1933_; lean_object* v_vs_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_ks_1933_ = lean_ctor_get(v_x_1908_, 0);
lean_inc_ref(v_ks_1933_);
v_vs_1934_ = lean_ctor_get(v_x_1908_, 1);
lean_inc_ref(v_vs_1934_);
lean_dec_ref(v_x_1908_);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___redArg(v_ks_1933_, v_vs_1934_, v___x_1935_, v_x_1910_);
lean_dec_ref(v_vs_1934_);
lean_dec_ref(v_ks_1933_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
size_t v_x_4877__boxed_1940_; lean_object* v_res_1941_; 
v_x_4877__boxed_1940_ = lean_unbox_usize(v_x_1938_);
lean_dec(v_x_1938_);
v_res_1941_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___redArg(v_x_1937_, v_x_4877__boxed_1940_, v_x_1939_);
lean_dec_ref(v_x_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(lean_object* v_x_1942_, lean_object* v_x_1943_){
_start:
{
uint64_t v___x_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = l_Lean_Meta_Grind_instHashableCanonArgKey_hash(v_x_1943_);
v___x_1945_ = lean_uint64_to_usize(v___x_1944_);
v___x_1946_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___redArg(v_x_1942_, v___x_1945_, v_x_1943_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg___boxed(lean_object* v_x_1947_, lean_object* v_x_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(v_x_1947_, v_x_1948_);
lean_dec_ref(v_x_1948_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(lean_object* v_parent_1950_, lean_object* v_f_1951_, lean_object* v_i_1952_, lean_object* v_e_1953_, uint8_t v_useIsDefEqBounded_1954_, uint8_t v_isInst_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v_toGoalState_1968_; lean_object* v_canon_1969_; lean_object* v_canonArg_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1967_ = lean_st_ref_get(v_a_1956_);
v_toGoalState_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc_ref(v_toGoalState_1968_);
lean_dec(v___x_1967_);
v_canon_1969_ = lean_ctor_get(v_toGoalState_1968_, 1);
lean_inc_ref(v_canon_1969_);
lean_dec_ref(v_toGoalState_1968_);
v_canonArg_1970_ = lean_ctor_get(v_canon_1969_, 3);
lean_inc_ref(v_canonArg_1970_);
lean_dec_ref(v_canon_1969_);
lean_inc_ref(v_e_1953_);
lean_inc(v_i_1952_);
lean_inc_ref(v_f_1951_);
v___x_1971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1971_, 0, v_f_1951_);
lean_ctor_set(v___x_1971_, 1, v_i_1952_);
lean_ctor_set(v___x_1971_, 2, v_e_1953_);
v___x_1972_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(v_canonArg_1970_, v___x_1971_);
if (lean_obj_tag(v___x_1972_) == 1)
{
lean_object* v_val_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v___x_1971_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_e_1953_);
lean_dec(v_i_1952_);
lean_dec_ref(v_f_1951_);
lean_dec_ref(v_parent_1950_);
v_val_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_val_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 0);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_val_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v___x_1981_; 
lean_dec(v___x_1972_);
lean_inc(v_a_1956_);
v___x_1981_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_go(v_parent_1950_, v_f_1951_, v_i_1952_, v_e_1953_, v_useIsDefEqBounded_1954_, v_isInst_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2040_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_2040_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2040_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v_toGoalState_1987_; lean_object* v_canon_1988_; lean_object* v_mvarId_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2038_; 
v___x_1986_ = lean_st_ref_take(v_a_1956_);
v_toGoalState_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc_ref(v_toGoalState_1987_);
v_canon_1988_ = lean_ctor_get(v_toGoalState_1987_, 1);
lean_inc_ref(v_canon_1988_);
v_mvarId_1989_ = lean_ctor_get(v___x_1986_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v___x_1986_, 0);
lean_dec(v_unused_2039_);
v___x_1991_ = v___x_1986_;
v_isShared_1992_ = v_isSharedCheck_2038_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_mvarId_1989_);
lean_dec(v___x_1986_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2038_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_nextDeclIdx_1993_; lean_object* v_enodeMap_1994_; lean_object* v_exprs_1995_; lean_object* v_parents_1996_; lean_object* v_congrTable_1997_; lean_object* v_appMap_1998_; lean_object* v_indicesFound_1999_; lean_object* v_newFacts_2000_; uint8_t v_inconsistent_2001_; lean_object* v_nextIdx_2002_; lean_object* v_newRawFacts_2003_; lean_object* v_facts_2004_; lean_object* v_extThms_2005_; lean_object* v_ematch_2006_; lean_object* v_inj_2007_; lean_object* v_split_2008_; lean_object* v_clean_2009_; lean_object* v_sstates_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2036_; 
v_nextDeclIdx_1993_ = lean_ctor_get(v_toGoalState_1987_, 0);
v_enodeMap_1994_ = lean_ctor_get(v_toGoalState_1987_, 2);
v_exprs_1995_ = lean_ctor_get(v_toGoalState_1987_, 3);
v_parents_1996_ = lean_ctor_get(v_toGoalState_1987_, 4);
v_congrTable_1997_ = lean_ctor_get(v_toGoalState_1987_, 5);
v_appMap_1998_ = lean_ctor_get(v_toGoalState_1987_, 6);
v_indicesFound_1999_ = lean_ctor_get(v_toGoalState_1987_, 7);
v_newFacts_2000_ = lean_ctor_get(v_toGoalState_1987_, 8);
v_inconsistent_2001_ = lean_ctor_get_uint8(v_toGoalState_1987_, sizeof(void*)*18);
v_nextIdx_2002_ = lean_ctor_get(v_toGoalState_1987_, 9);
v_newRawFacts_2003_ = lean_ctor_get(v_toGoalState_1987_, 10);
v_facts_2004_ = lean_ctor_get(v_toGoalState_1987_, 11);
v_extThms_2005_ = lean_ctor_get(v_toGoalState_1987_, 12);
v_ematch_2006_ = lean_ctor_get(v_toGoalState_1987_, 13);
v_inj_2007_ = lean_ctor_get(v_toGoalState_1987_, 14);
v_split_2008_ = lean_ctor_get(v_toGoalState_1987_, 15);
v_clean_2009_ = lean_ctor_get(v_toGoalState_1987_, 16);
v_sstates_2010_ = lean_ctor_get(v_toGoalState_1987_, 17);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_toGoalState_1987_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v_toGoalState_1987_, 1);
lean_dec(v_unused_2037_);
v___x_2012_ = v_toGoalState_1987_;
v_isShared_2013_ = v_isSharedCheck_2036_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_sstates_2010_);
lean_inc(v_clean_2009_);
lean_inc(v_split_2008_);
lean_inc(v_inj_2007_);
lean_inc(v_ematch_2006_);
lean_inc(v_extThms_2005_);
lean_inc(v_facts_2004_);
lean_inc(v_newRawFacts_2003_);
lean_inc(v_nextIdx_2002_);
lean_inc(v_newFacts_2000_);
lean_inc(v_indicesFound_1999_);
lean_inc(v_appMap_1998_);
lean_inc(v_congrTable_1997_);
lean_inc(v_parents_1996_);
lean_inc(v_exprs_1995_);
lean_inc(v_enodeMap_1994_);
lean_inc(v_nextDeclIdx_1993_);
lean_dec(v_toGoalState_1987_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2036_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_argMap_2014_; lean_object* v_canon_2015_; lean_object* v_proofCanon_2016_; lean_object* v_canonArg_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2035_; 
v_argMap_2014_ = lean_ctor_get(v_canon_1988_, 0);
v_canon_2015_ = lean_ctor_get(v_canon_1988_, 1);
v_proofCanon_2016_ = lean_ctor_get(v_canon_1988_, 2);
v_canonArg_2017_ = lean_ctor_get(v_canon_1988_, 3);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_canon_1988_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2019_ = v_canon_1988_;
v_isShared_2020_ = v_isSharedCheck_2035_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_canonArg_2017_);
lean_inc(v_proofCanon_2016_);
lean_inc(v_canon_2015_);
lean_inc(v_argMap_2014_);
lean_dec(v_canon_1988_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2035_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_inc(v_a_1982_);
v___x_2021_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(v_canonArg_2017_, v___x_1971_, v_a_1982_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 3, v___x_2021_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_argMap_2014_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_canon_2015_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_proofCanon_2016_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v___x_2023_);
v___x_2025_ = v___x_2012_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_nextDeclIdx_1993_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_enodeMap_1994_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v_exprs_1995_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v_parents_1996_);
lean_ctor_set(v_reuseFailAlloc_2033_, 5, v_congrTable_1997_);
lean_ctor_set(v_reuseFailAlloc_2033_, 6, v_appMap_1998_);
lean_ctor_set(v_reuseFailAlloc_2033_, 7, v_indicesFound_1999_);
lean_ctor_set(v_reuseFailAlloc_2033_, 8, v_newFacts_2000_);
lean_ctor_set(v_reuseFailAlloc_2033_, 9, v_nextIdx_2002_);
lean_ctor_set(v_reuseFailAlloc_2033_, 10, v_newRawFacts_2003_);
lean_ctor_set(v_reuseFailAlloc_2033_, 11, v_facts_2004_);
lean_ctor_set(v_reuseFailAlloc_2033_, 12, v_extThms_2005_);
lean_ctor_set(v_reuseFailAlloc_2033_, 13, v_ematch_2006_);
lean_ctor_set(v_reuseFailAlloc_2033_, 14, v_inj_2007_);
lean_ctor_set(v_reuseFailAlloc_2033_, 15, v_split_2008_);
lean_ctor_set(v_reuseFailAlloc_2033_, 16, v_clean_2009_);
lean_ctor_set(v_reuseFailAlloc_2033_, 17, v_sstates_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2033_, sizeof(void*)*18, v_inconsistent_2001_);
v___x_2025_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2025_);
v___x_2027_ = v___x_1991_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_mvarId_1989_);
v___x_2027_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_st_ref_set(v_a_1956_, v___x_2027_);
lean_dec(v_a_1956_);
if (v_isShared_1985_ == 0)
{
v___x_2030_ = v___x_1984_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_1982_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
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
lean_dec_ref(v___x_1971_);
lean_dec(v_a_1956_);
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore___boxed(lean_object** _args){
lean_object* v_parent_2041_ = _args[0];
lean_object* v_f_2042_ = _args[1];
lean_object* v_i_2043_ = _args[2];
lean_object* v_e_2044_ = _args[3];
lean_object* v_useIsDefEqBounded_2045_ = _args[4];
lean_object* v_isInst_2046_ = _args[5];
lean_object* v_a_2047_ = _args[6];
lean_object* v_a_2048_ = _args[7];
lean_object* v_a_2049_ = _args[8];
lean_object* v_a_2050_ = _args[9];
lean_object* v_a_2051_ = _args[10];
lean_object* v_a_2052_ = _args[11];
lean_object* v_a_2053_ = _args[12];
lean_object* v_a_2054_ = _args[13];
lean_object* v_a_2055_ = _args[14];
lean_object* v_a_2056_ = _args[15];
lean_object* v_a_2057_ = _args[16];
_start:
{
uint8_t v_useIsDefEqBounded_boxed_2058_; uint8_t v_isInst_boxed_2059_; lean_object* v_res_2060_; 
v_useIsDefEqBounded_boxed_2058_ = lean_unbox(v_useIsDefEqBounded_2045_);
v_isInst_boxed_2059_ = lean_unbox(v_isInst_2046_);
v_res_2060_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(v_parent_2041_, v_f_2042_, v_i_2043_, v_e_2044_, v_useIsDefEqBounded_boxed_2058_, v_isInst_boxed_2059_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0(lean_object* v_00_u03b2_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___redArg(v_x_2062_, v_x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0___boxed(lean_object* v_00_u03b2_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0(v_00_u03b2_2065_, v_x_2066_, v_x_2067_);
lean_dec_ref(v_x_2067_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1(lean_object* v_00_u03b2_2069_, lean_object* v_x_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1___redArg(v_x_2070_, v_x_2071_, v_x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0(lean_object* v_00_u03b2_2074_, lean_object* v_x_2075_, size_t v_x_2076_, lean_object* v_x_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___redArg(v_x_2075_, v_x_2076_, v_x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
size_t v_x_5092__boxed_2083_; lean_object* v_res_2084_; 
v_x_5092__boxed_2083_ = lean_unbox_usize(v_x_2081_);
lean_dec(v_x_2081_);
v_res_2084_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0(v_00_u03b2_2079_, v_x_2080_, v_x_5092__boxed_2083_, v_x_2082_);
lean_dec_ref(v_x_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2(lean_object* v_00_u03b2_2085_, lean_object* v_x_2086_, size_t v_x_2087_, size_t v_x_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___redArg(v_x_2086_, v_x_2087_, v_x_2088_, v_x_2089_, v_x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
size_t v_x_5103__boxed_2098_; size_t v_x_5104__boxed_2099_; lean_object* v_res_2100_; 
v_x_5103__boxed_2098_ = lean_unbox_usize(v_x_2094_);
lean_dec(v_x_2094_);
v_x_5104__boxed_2099_ = lean_unbox_usize(v_x_2095_);
lean_dec(v_x_2095_);
v_res_2100_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2(v_00_u03b2_2092_, v_x_2093_, v_x_5103__boxed_2098_, v_x_5104__boxed_2099_, v_x_2096_, v_x_2097_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2101_, lean_object* v_keys_2102_, lean_object* v_vals_2103_, lean_object* v_heq_2104_, lean_object* v_i_2105_, lean_object* v_k_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___redArg(v_keys_2102_, v_vals_2103_, v_i_2105_, v_k_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2108_, lean_object* v_keys_2109_, lean_object* v_vals_2110_, lean_object* v_heq_2111_, lean_object* v_i_2112_, lean_object* v_k_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__0_spec__0_spec__1(v_00_u03b2_2108_, v_keys_2109_, v_vals_2110_, v_heq_2111_, v_i_2112_, v_k_2113_);
lean_dec_ref(v_k_2113_);
lean_dec_ref(v_vals_2110_);
lean_dec_ref(v_keys_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2115_, lean_object* v_n_2116_, lean_object* v_k_2117_, lean_object* v_v_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4___redArg(v_n_2116_, v_k_2117_, v_v_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2120_, size_t v_depth_2121_, lean_object* v_keys_2122_, lean_object* v_vals_2123_, lean_object* v_heq_2124_, lean_object* v_i_2125_, lean_object* v_entries_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___redArg(v_depth_2121_, v_keys_2122_, v_vals_2123_, v_i_2125_, v_entries_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2128_, lean_object* v_depth_2129_, lean_object* v_keys_2130_, lean_object* v_vals_2131_, lean_object* v_heq_2132_, lean_object* v_i_2133_, lean_object* v_entries_2134_){
_start:
{
size_t v_depth_boxed_2135_; lean_object* v_res_2136_; 
v_depth_boxed_2135_ = lean_unbox_usize(v_depth_2129_);
lean_dec(v_depth_2129_);
v_res_2136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__5(v_00_u03b2_2128_, v_depth_boxed_2135_, v_keys_2130_, v_vals_2131_, v_heq_2132_, v_i_2133_, v_entries_2134_);
lean_dec_ref(v_vals_2131_);
lean_dec_ref(v_keys_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2138_, v_x_2139_, v_x_2140_, v_x_2141_);
return v___x_2142_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0(void){
_start:
{
uint8_t v___x_2143_; uint64_t v___x_2144_; 
v___x_2143_ = 1;
v___x_2144_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType(lean_object* v_parent_2145_, lean_object* v_f_2146_, lean_object* v_i_2147_, lean_object* v_e_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v___x_2160_; uint8_t v_foApprox_2161_; uint8_t v_ctxApprox_2162_; uint8_t v_quasiPatternApprox_2163_; uint8_t v_constApprox_2164_; uint8_t v_isDefEqStuckEx_2165_; uint8_t v_unificationHints_2166_; uint8_t v_proofIrrelevance_2167_; uint8_t v_assignSyntheticOpaque_2168_; uint8_t v_offsetCnstrs_2169_; uint8_t v_etaStruct_2170_; uint8_t v_univApprox_2171_; uint8_t v_iota_2172_; uint8_t v_beta_2173_; uint8_t v_proj_2174_; uint8_t v_zeta_2175_; uint8_t v_zetaDelta_2176_; uint8_t v_zetaUnused_2177_; uint8_t v_zetaHave_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2227_; 
v___x_2160_ = l_Lean_Meta_Context_config(v_a_2155_);
v_foApprox_2161_ = lean_ctor_get_uint8(v___x_2160_, 0);
v_ctxApprox_2162_ = lean_ctor_get_uint8(v___x_2160_, 1);
v_quasiPatternApprox_2163_ = lean_ctor_get_uint8(v___x_2160_, 2);
v_constApprox_2164_ = lean_ctor_get_uint8(v___x_2160_, 3);
v_isDefEqStuckEx_2165_ = lean_ctor_get_uint8(v___x_2160_, 4);
v_unificationHints_2166_ = lean_ctor_get_uint8(v___x_2160_, 5);
v_proofIrrelevance_2167_ = lean_ctor_get_uint8(v___x_2160_, 6);
v_assignSyntheticOpaque_2168_ = lean_ctor_get_uint8(v___x_2160_, 7);
v_offsetCnstrs_2169_ = lean_ctor_get_uint8(v___x_2160_, 8);
v_etaStruct_2170_ = lean_ctor_get_uint8(v___x_2160_, 10);
v_univApprox_2171_ = lean_ctor_get_uint8(v___x_2160_, 11);
v_iota_2172_ = lean_ctor_get_uint8(v___x_2160_, 12);
v_beta_2173_ = lean_ctor_get_uint8(v___x_2160_, 13);
v_proj_2174_ = lean_ctor_get_uint8(v___x_2160_, 14);
v_zeta_2175_ = lean_ctor_get_uint8(v___x_2160_, 15);
v_zetaDelta_2176_ = lean_ctor_get_uint8(v___x_2160_, 16);
v_zetaUnused_2177_ = lean_ctor_get_uint8(v___x_2160_, 17);
v_zetaHave_2178_ = lean_ctor_get_uint8(v___x_2160_, 18);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2180_ = v___x_2160_;
v_isShared_2181_ = v_isSharedCheck_2227_;
goto v_resetjp_2179_;
}
else
{
lean_dec(v___x_2160_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2227_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
uint8_t v_trackZetaDelta_2182_; lean_object* v_zetaDeltaSet_2183_; lean_object* v_lctx_2184_; lean_object* v_localInstances_2185_; lean_object* v_defEqCtx_x3f_2186_; lean_object* v_synthPendingDepth_2187_; lean_object* v_canUnfold_x3f_2188_; uint8_t v_univApprox_2189_; uint8_t v_inTypeClassResolution_2190_; uint8_t v_cacheInferType_2191_; uint8_t v___x_2192_; lean_object* v_config_2194_; 
v_trackZetaDelta_2182_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*7);
v_zetaDeltaSet_2183_ = lean_ctor_get(v_a_2155_, 1);
lean_inc(v_zetaDeltaSet_2183_);
v_lctx_2184_ = lean_ctor_get(v_a_2155_, 2);
lean_inc_ref(v_lctx_2184_);
v_localInstances_2185_ = lean_ctor_get(v_a_2155_, 3);
lean_inc_ref(v_localInstances_2185_);
v_defEqCtx_x3f_2186_ = lean_ctor_get(v_a_2155_, 4);
lean_inc(v_defEqCtx_x3f_2186_);
v_synthPendingDepth_2187_ = lean_ctor_get(v_a_2155_, 5);
lean_inc(v_synthPendingDepth_2187_);
v_canUnfold_x3f_2188_ = lean_ctor_get(v_a_2155_, 6);
lean_inc(v_canUnfold_x3f_2188_);
v_univApprox_2189_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2190_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*7 + 2);
v_cacheInferType_2191_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*7 + 3);
v___x_2192_ = 1;
if (v_isShared_2181_ == 0)
{
v_config_2194_ = v___x_2180_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 0, v_foApprox_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 1, v_ctxApprox_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 2, v_quasiPatternApprox_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 3, v_constApprox_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 4, v_isDefEqStuckEx_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 5, v_unificationHints_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 6, v_proofIrrelevance_2167_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 7, v_assignSyntheticOpaque_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 8, v_offsetCnstrs_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 10, v_etaStruct_2170_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 11, v_univApprox_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 12, v_iota_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 13, v_beta_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 14, v_proj_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 15, v_zeta_2175_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 16, v_zetaDelta_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 17, v_zetaUnused_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2226_, 18, v_zetaHave_2178_);
v_config_2194_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
uint64_t v___x_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2218_; 
lean_ctor_set_uint8(v_config_2194_, 9, v___x_2192_);
v___x_2195_ = l_Lean_Meta_Context_configKey(v_a_2155_);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_a_2155_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; lean_object* v_unused_2220_; lean_object* v_unused_2221_; lean_object* v_unused_2222_; lean_object* v_unused_2223_; lean_object* v_unused_2224_; lean_object* v_unused_2225_; 
v_unused_2219_ = lean_ctor_get(v_a_2155_, 6);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_a_2155_, 5);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_a_2155_, 4);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_a_2155_, 3);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_a_2155_, 2);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_a_2155_, 1);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_a_2155_, 0);
lean_dec(v_unused_2225_);
v___x_2197_ = v_a_2155_;
v_isShared_2198_ = v_isSharedCheck_2218_;
goto v_resetjp_2196_;
}
else
{
lean_dec(v_a_2155_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2218_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
uint64_t v___x_2199_; uint64_t v___x_2200_; uint8_t v___x_2201_; uint64_t v___x_2202_; uint64_t v___x_2203_; uint64_t v_key_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2199_ = 2ULL;
v___x_2200_ = lean_uint64_shift_right(v___x_2195_, v___x_2199_);
v___x_2201_ = 0;
v___x_2202_ = lean_uint64_shift_left(v___x_2200_, v___x_2199_);
v___x_2203_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0);
v_key_2204_ = lean_uint64_lor(v___x_2202_, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2205_, 0, v_config_2194_);
lean_ctor_set_uint64(v___x_2205_, sizeof(void*)*1, v_key_2204_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2205_);
v___x_2207_ = v___x_2197_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_zetaDeltaSet_2183_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_lctx_2184_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v_localInstances_2185_);
lean_ctor_set(v_reuseFailAlloc_2217_, 4, v_defEqCtx_x3f_2186_);
lean_ctor_set(v_reuseFailAlloc_2217_, 5, v_synthPendingDepth_2187_);
lean_ctor_set(v_reuseFailAlloc_2217_, 6, v_canUnfold_x3f_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2217_, sizeof(void*)*7, v_trackZetaDelta_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2217_, sizeof(void*)*7 + 1, v_univApprox_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2217_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2217_, sizeof(void*)*7 + 3, v_cacheInferType_2191_);
v___x_2207_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; 
v___x_2208_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(v_parent_2145_, v_f_2146_, v_i_2147_, v_e_2148_, v___x_2201_, v___x_2201_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v___x_2207_, v_a_2156_, v_a_2157_, v_a_2158_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
return v___x_2208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___boxed(lean_object* v_parent_2228_, lean_object* v_f_2229_, lean_object* v_i_2230_, lean_object* v_e_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType(v_parent_2228_, v_f_2229_, v_i_2230_, v_e_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
return v_res_2243_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0(void){
_start:
{
uint8_t v___x_2244_; uint64_t v___x_2245_; 
v___x_2244_ = 3;
v___x_2245_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst(lean_object* v_parent_2246_, lean_object* v_f_2247_, lean_object* v_i_2248_, lean_object* v_e_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; uint8_t v_foApprox_2262_; uint8_t v_ctxApprox_2263_; uint8_t v_quasiPatternApprox_2264_; uint8_t v_constApprox_2265_; uint8_t v_isDefEqStuckEx_2266_; uint8_t v_unificationHints_2267_; uint8_t v_proofIrrelevance_2268_; uint8_t v_assignSyntheticOpaque_2269_; uint8_t v_offsetCnstrs_2270_; uint8_t v_etaStruct_2271_; uint8_t v_univApprox_2272_; uint8_t v_iota_2273_; uint8_t v_beta_2274_; uint8_t v_proj_2275_; uint8_t v_zeta_2276_; uint8_t v_zetaDelta_2277_; uint8_t v_zetaUnused_2278_; uint8_t v_zetaHave_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2328_; 
v___x_2261_ = l_Lean_Meta_Context_config(v_a_2256_);
v_foApprox_2262_ = lean_ctor_get_uint8(v___x_2261_, 0);
v_ctxApprox_2263_ = lean_ctor_get_uint8(v___x_2261_, 1);
v_quasiPatternApprox_2264_ = lean_ctor_get_uint8(v___x_2261_, 2);
v_constApprox_2265_ = lean_ctor_get_uint8(v___x_2261_, 3);
v_isDefEqStuckEx_2266_ = lean_ctor_get_uint8(v___x_2261_, 4);
v_unificationHints_2267_ = lean_ctor_get_uint8(v___x_2261_, 5);
v_proofIrrelevance_2268_ = lean_ctor_get_uint8(v___x_2261_, 6);
v_assignSyntheticOpaque_2269_ = lean_ctor_get_uint8(v___x_2261_, 7);
v_offsetCnstrs_2270_ = lean_ctor_get_uint8(v___x_2261_, 8);
v_etaStruct_2271_ = lean_ctor_get_uint8(v___x_2261_, 10);
v_univApprox_2272_ = lean_ctor_get_uint8(v___x_2261_, 11);
v_iota_2273_ = lean_ctor_get_uint8(v___x_2261_, 12);
v_beta_2274_ = lean_ctor_get_uint8(v___x_2261_, 13);
v_proj_2275_ = lean_ctor_get_uint8(v___x_2261_, 14);
v_zeta_2276_ = lean_ctor_get_uint8(v___x_2261_, 15);
v_zetaDelta_2277_ = lean_ctor_get_uint8(v___x_2261_, 16);
v_zetaUnused_2278_ = lean_ctor_get_uint8(v___x_2261_, 17);
v_zetaHave_2279_ = lean_ctor_get_uint8(v___x_2261_, 18);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2281_ = v___x_2261_;
v_isShared_2282_ = v_isSharedCheck_2328_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v___x_2261_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2328_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
uint8_t v_trackZetaDelta_2283_; lean_object* v_zetaDeltaSet_2284_; lean_object* v_lctx_2285_; lean_object* v_localInstances_2286_; lean_object* v_defEqCtx_x3f_2287_; lean_object* v_synthPendingDepth_2288_; lean_object* v_canUnfold_x3f_2289_; uint8_t v_univApprox_2290_; uint8_t v_inTypeClassResolution_2291_; uint8_t v_cacheInferType_2292_; uint8_t v___x_2293_; lean_object* v_config_2295_; 
v_trackZetaDelta_2283_ = lean_ctor_get_uint8(v_a_2256_, sizeof(void*)*7);
v_zetaDeltaSet_2284_ = lean_ctor_get(v_a_2256_, 1);
lean_inc(v_zetaDeltaSet_2284_);
v_lctx_2285_ = lean_ctor_get(v_a_2256_, 2);
lean_inc_ref(v_lctx_2285_);
v_localInstances_2286_ = lean_ctor_get(v_a_2256_, 3);
lean_inc_ref(v_localInstances_2286_);
v_defEqCtx_x3f_2287_ = lean_ctor_get(v_a_2256_, 4);
lean_inc(v_defEqCtx_x3f_2287_);
v_synthPendingDepth_2288_ = lean_ctor_get(v_a_2256_, 5);
lean_inc(v_synthPendingDepth_2288_);
v_canUnfold_x3f_2289_ = lean_ctor_get(v_a_2256_, 6);
lean_inc(v_canUnfold_x3f_2289_);
v_univApprox_2290_ = lean_ctor_get_uint8(v_a_2256_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2291_ = lean_ctor_get_uint8(v_a_2256_, sizeof(void*)*7 + 2);
v_cacheInferType_2292_ = lean_ctor_get_uint8(v_a_2256_, sizeof(void*)*7 + 3);
v___x_2293_ = 3;
if (v_isShared_2282_ == 0)
{
v_config_2295_ = v___x_2281_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 0, v_foApprox_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 1, v_ctxApprox_2263_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 2, v_quasiPatternApprox_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 3, v_constApprox_2265_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 4, v_isDefEqStuckEx_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 5, v_unificationHints_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 6, v_proofIrrelevance_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 7, v_assignSyntheticOpaque_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 8, v_offsetCnstrs_2270_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 10, v_etaStruct_2271_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 11, v_univApprox_2272_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 12, v_iota_2273_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 13, v_beta_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 14, v_proj_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 15, v_zeta_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 16, v_zetaDelta_2277_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 17, v_zetaUnused_2278_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 18, v_zetaHave_2279_);
v_config_2295_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
uint64_t v___x_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2319_; 
lean_ctor_set_uint8(v_config_2295_, 9, v___x_2293_);
v___x_2296_ = l_Lean_Meta_Context_configKey(v_a_2256_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_a_2256_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; lean_object* v_unused_2325_; lean_object* v_unused_2326_; 
v_unused_2320_ = lean_ctor_get(v_a_2256_, 6);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_a_2256_, 5);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_a_2256_, 4);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_a_2256_, 3);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_a_2256_, 2);
lean_dec(v_unused_2324_);
v_unused_2325_ = lean_ctor_get(v_a_2256_, 1);
lean_dec(v_unused_2325_);
v_unused_2326_ = lean_ctor_get(v_a_2256_, 0);
lean_dec(v_unused_2326_);
v___x_2298_ = v_a_2256_;
v_isShared_2299_ = v_isSharedCheck_2319_;
goto v_resetjp_2297_;
}
else
{
lean_dec(v_a_2256_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2319_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
uint64_t v___x_2300_; uint64_t v___x_2301_; uint8_t v___x_2302_; uint64_t v___x_2303_; uint64_t v___x_2304_; uint64_t v_key_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2300_ = 2ULL;
v___x_2301_ = lean_uint64_shift_right(v___x_2296_, v___x_2300_);
v___x_2302_ = 1;
v___x_2303_ = lean_uint64_shift_left(v___x_2301_, v___x_2300_);
v___x_2304_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0);
v_key_2305_ = lean_uint64_lor(v___x_2303_, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2306_, 0, v_config_2295_);
lean_ctor_set_uint64(v___x_2306_, sizeof(void*)*1, v_key_2305_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2306_);
v___x_2308_ = v___x_2298_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_zetaDeltaSet_2284_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_lctx_2285_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_localInstances_2286_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_defEqCtx_x3f_2287_);
lean_ctor_set(v_reuseFailAlloc_2318_, 5, v_synthPendingDepth_2288_);
lean_ctor_set(v_reuseFailAlloc_2318_, 6, v_canUnfold_x3f_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2318_, sizeof(void*)*7, v_trackZetaDelta_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2318_, sizeof(void*)*7 + 1, v_univApprox_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2318_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2318_, sizeof(void*)*7 + 3, v_cacheInferType_2292_);
v___x_2308_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; 
v___x_2309_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(v_parent_2246_, v_f_2247_, v_i_2248_, v_e_2249_, v___x_2302_, v___x_2302_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v___x_2308_, v_a_2257_, v_a_2258_, v_a_2259_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
return v___x_2309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___boxed(lean_object* v_parent_2329_, lean_object* v_f_2330_, lean_object* v_i_2331_, lean_object* v_e_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst(v_parent_2329_, v_f_2330_, v_i_2331_, v_e_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_);
return v_res_2344_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0(void){
_start:
{
uint8_t v___x_2345_; uint64_t v___x_2346_; 
v___x_2345_ = 2;
v___x_2346_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit(lean_object* v_parent_2347_, lean_object* v_f_2348_, lean_object* v_i_2349_, lean_object* v_e_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; uint8_t v_foApprox_2363_; uint8_t v_ctxApprox_2364_; uint8_t v_quasiPatternApprox_2365_; uint8_t v_constApprox_2366_; uint8_t v_isDefEqStuckEx_2367_; uint8_t v_unificationHints_2368_; uint8_t v_proofIrrelevance_2369_; uint8_t v_assignSyntheticOpaque_2370_; uint8_t v_offsetCnstrs_2371_; uint8_t v_etaStruct_2372_; uint8_t v_univApprox_2373_; uint8_t v_iota_2374_; uint8_t v_beta_2375_; uint8_t v_proj_2376_; uint8_t v_zeta_2377_; uint8_t v_zetaDelta_2378_; uint8_t v_zetaUnused_2379_; uint8_t v_zetaHave_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2430_; 
v___x_2362_ = l_Lean_Meta_Context_config(v_a_2357_);
v_foApprox_2363_ = lean_ctor_get_uint8(v___x_2362_, 0);
v_ctxApprox_2364_ = lean_ctor_get_uint8(v___x_2362_, 1);
v_quasiPatternApprox_2365_ = lean_ctor_get_uint8(v___x_2362_, 2);
v_constApprox_2366_ = lean_ctor_get_uint8(v___x_2362_, 3);
v_isDefEqStuckEx_2367_ = lean_ctor_get_uint8(v___x_2362_, 4);
v_unificationHints_2368_ = lean_ctor_get_uint8(v___x_2362_, 5);
v_proofIrrelevance_2369_ = lean_ctor_get_uint8(v___x_2362_, 6);
v_assignSyntheticOpaque_2370_ = lean_ctor_get_uint8(v___x_2362_, 7);
v_offsetCnstrs_2371_ = lean_ctor_get_uint8(v___x_2362_, 8);
v_etaStruct_2372_ = lean_ctor_get_uint8(v___x_2362_, 10);
v_univApprox_2373_ = lean_ctor_get_uint8(v___x_2362_, 11);
v_iota_2374_ = lean_ctor_get_uint8(v___x_2362_, 12);
v_beta_2375_ = lean_ctor_get_uint8(v___x_2362_, 13);
v_proj_2376_ = lean_ctor_get_uint8(v___x_2362_, 14);
v_zeta_2377_ = lean_ctor_get_uint8(v___x_2362_, 15);
v_zetaDelta_2378_ = lean_ctor_get_uint8(v___x_2362_, 16);
v_zetaUnused_2379_ = lean_ctor_get_uint8(v___x_2362_, 17);
v_zetaHave_2380_ = lean_ctor_get_uint8(v___x_2362_, 18);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2382_ = v___x_2362_;
v_isShared_2383_ = v_isSharedCheck_2430_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v___x_2362_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2430_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
uint8_t v_trackZetaDelta_2384_; lean_object* v_zetaDeltaSet_2385_; lean_object* v_lctx_2386_; lean_object* v_localInstances_2387_; lean_object* v_defEqCtx_x3f_2388_; lean_object* v_synthPendingDepth_2389_; lean_object* v_canUnfold_x3f_2390_; uint8_t v_univApprox_2391_; uint8_t v_inTypeClassResolution_2392_; uint8_t v_cacheInferType_2393_; uint8_t v___x_2394_; lean_object* v_config_2396_; 
v_trackZetaDelta_2384_ = lean_ctor_get_uint8(v_a_2357_, sizeof(void*)*7);
v_zetaDeltaSet_2385_ = lean_ctor_get(v_a_2357_, 1);
lean_inc(v_zetaDeltaSet_2385_);
v_lctx_2386_ = lean_ctor_get(v_a_2357_, 2);
lean_inc_ref(v_lctx_2386_);
v_localInstances_2387_ = lean_ctor_get(v_a_2357_, 3);
lean_inc_ref(v_localInstances_2387_);
v_defEqCtx_x3f_2388_ = lean_ctor_get(v_a_2357_, 4);
lean_inc(v_defEqCtx_x3f_2388_);
v_synthPendingDepth_2389_ = lean_ctor_get(v_a_2357_, 5);
lean_inc(v_synthPendingDepth_2389_);
v_canUnfold_x3f_2390_ = lean_ctor_get(v_a_2357_, 6);
lean_inc(v_canUnfold_x3f_2390_);
v_univApprox_2391_ = lean_ctor_get_uint8(v_a_2357_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2392_ = lean_ctor_get_uint8(v_a_2357_, sizeof(void*)*7 + 2);
v_cacheInferType_2393_ = lean_ctor_get_uint8(v_a_2357_, sizeof(void*)*7 + 3);
v___x_2394_ = 2;
if (v_isShared_2383_ == 0)
{
v_config_2396_ = v___x_2382_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 0, v_foApprox_2363_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 1, v_ctxApprox_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 2, v_quasiPatternApprox_2365_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 3, v_constApprox_2366_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 4, v_isDefEqStuckEx_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 5, v_unificationHints_2368_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 6, v_proofIrrelevance_2369_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 7, v_assignSyntheticOpaque_2370_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 8, v_offsetCnstrs_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 10, v_etaStruct_2372_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 11, v_univApprox_2373_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 12, v_iota_2374_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 13, v_beta_2375_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 14, v_proj_2376_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 15, v_zeta_2377_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 16, v_zetaDelta_2378_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 17, v_zetaUnused_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2429_, 18, v_zetaHave_2380_);
v_config_2396_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
uint64_t v___x_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2421_; 
lean_ctor_set_uint8(v_config_2396_, 9, v___x_2394_);
v___x_2397_ = l_Lean_Meta_Context_configKey(v_a_2357_);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_a_2357_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; lean_object* v_unused_2423_; lean_object* v_unused_2424_; lean_object* v_unused_2425_; lean_object* v_unused_2426_; lean_object* v_unused_2427_; lean_object* v_unused_2428_; 
v_unused_2422_ = lean_ctor_get(v_a_2357_, 6);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_a_2357_, 5);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_a_2357_, 4);
lean_dec(v_unused_2424_);
v_unused_2425_ = lean_ctor_get(v_a_2357_, 3);
lean_dec(v_unused_2425_);
v_unused_2426_ = lean_ctor_get(v_a_2357_, 2);
lean_dec(v_unused_2426_);
v_unused_2427_ = lean_ctor_get(v_a_2357_, 1);
lean_dec(v_unused_2427_);
v_unused_2428_ = lean_ctor_get(v_a_2357_, 0);
lean_dec(v_unused_2428_);
v___x_2399_ = v_a_2357_;
v_isShared_2400_ = v_isSharedCheck_2421_;
goto v_resetjp_2398_;
}
else
{
lean_dec(v_a_2357_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2421_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
uint64_t v___x_2401_; uint64_t v___x_2402_; uint8_t v___x_2403_; uint8_t v___x_2404_; uint64_t v___x_2405_; uint64_t v___x_2406_; uint64_t v_key_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2401_ = 2ULL;
v___x_2402_ = lean_uint64_shift_right(v___x_2397_, v___x_2401_);
v___x_2403_ = 1;
v___x_2404_ = 0;
v___x_2405_ = lean_uint64_shift_left(v___x_2402_, v___x_2401_);
v___x_2406_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0);
v_key_2407_ = lean_uint64_lor(v___x_2405_, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2408_, 0, v_config_2396_);
lean_ctor_set_uint64(v___x_2408_, sizeof(void*)*1, v_key_2407_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2408_);
v___x_2410_ = v___x_2399_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_zetaDeltaSet_2385_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v_lctx_2386_);
lean_ctor_set(v_reuseFailAlloc_2420_, 3, v_localInstances_2387_);
lean_ctor_set(v_reuseFailAlloc_2420_, 4, v_defEqCtx_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2420_, 5, v_synthPendingDepth_2389_);
lean_ctor_set(v_reuseFailAlloc_2420_, 6, v_canUnfold_x3f_2390_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*7, v_trackZetaDelta_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*7 + 1, v_univApprox_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2420_, sizeof(void*)*7 + 3, v_cacheInferType_2393_);
v___x_2410_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; 
v___x_2411_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(v_parent_2347_, v_f_2348_, v_i_2349_, v_e_2350_, v___x_2403_, v___x_2404_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v___x_2410_, v_a_2358_, v_a_2359_, v_a_2360_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
else
{
return v___x_2411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___boxed(lean_object* v_parent_2431_, lean_object* v_f_2432_, lean_object* v_i_2433_, lean_object* v_e_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit(v_parent_2431_, v_f_2432_, v_i_2433_, v_e_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorIdx(uint8_t v_x_2447_){
_start:
{
switch(v_x_2447_)
{
case 0:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_unsigned_to_nat(0u);
return v___x_2448_;
}
case 1:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_unsigned_to_nat(1u);
return v___x_2449_;
}
case 2:
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_unsigned_to_nat(2u);
return v___x_2450_;
}
default: 
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_unsigned_to_nat(3u);
return v___x_2451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorIdx___boxed(lean_object* v_x_2452_){
_start:
{
uint8_t v_x_boxed_2453_; lean_object* v_res_2454_; 
v_x_boxed_2453_ = lean_unbox(v_x_2452_);
v_res_2454_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorIdx(v_x_boxed_2453_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(uint8_t v_x_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorIdx(v_x_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx___boxed(lean_object* v_x_2457_){
_start:
{
uint8_t v_x_4__boxed_2458_; lean_object* v_res_2459_; 
v_x_4__boxed_2458_ = lean_unbox(v_x_2457_);
v_res_2459_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_toCtorIdx(v_x_4__boxed_2458_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim___redArg(lean_object* v_k_2460_){
_start:
{
lean_inc(v_k_2460_);
return v_k_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim___redArg___boxed(lean_object* v_k_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim___redArg(v_k_2461_);
lean_dec(v_k_2461_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim(lean_object* v_motive_2463_, lean_object* v_ctorIdx_2464_, uint8_t v_t_2465_, lean_object* v_h_2466_, lean_object* v_k_2467_){
_start:
{
lean_inc(v_k_2467_);
return v_k_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim___boxed(lean_object* v_motive_2468_, lean_object* v_ctorIdx_2469_, lean_object* v_t_2470_, lean_object* v_h_2471_, lean_object* v_k_2472_){
_start:
{
uint8_t v_t_boxed_2473_; lean_object* v_res_2474_; 
v_t_boxed_2473_ = lean_unbox(v_t_2470_);
v_res_2474_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_ctorElim(v_motive_2468_, v_ctorIdx_2469_, v_t_boxed_2473_, v_h_2471_, v_k_2472_);
lean_dec(v_k_2472_);
lean_dec(v_ctorIdx_2469_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim___redArg(lean_object* v_canonType_2475_){
_start:
{
lean_inc(v_canonType_2475_);
return v_canonType_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim___redArg___boxed(lean_object* v_canonType_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim___redArg(v_canonType_2476_);
lean_dec(v_canonType_2476_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim(lean_object* v_motive_2478_, uint8_t v_t_2479_, lean_object* v_h_2480_, lean_object* v_canonType_2481_){
_start:
{
lean_inc(v_canonType_2481_);
return v_canonType_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim___boxed(lean_object* v_motive_2482_, lean_object* v_t_2483_, lean_object* v_h_2484_, lean_object* v_canonType_2485_){
_start:
{
uint8_t v_t_boxed_2486_; lean_object* v_res_2487_; 
v_t_boxed_2486_ = lean_unbox(v_t_2483_);
v_res_2487_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonType_elim(v_motive_2482_, v_t_boxed_2486_, v_h_2484_, v_canonType_2485_);
lean_dec(v_canonType_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim___redArg(lean_object* v_canonInst_2488_){
_start:
{
lean_inc(v_canonInst_2488_);
return v_canonInst_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim___redArg___boxed(lean_object* v_canonInst_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim___redArg(v_canonInst_2489_);
lean_dec(v_canonInst_2489_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim(lean_object* v_motive_2491_, uint8_t v_t_2492_, lean_object* v_h_2493_, lean_object* v_canonInst_2494_){
_start:
{
lean_inc(v_canonInst_2494_);
return v_canonInst_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim___boxed(lean_object* v_motive_2495_, lean_object* v_t_2496_, lean_object* v_h_2497_, lean_object* v_canonInst_2498_){
_start:
{
uint8_t v_t_boxed_2499_; lean_object* v_res_2500_; 
v_t_boxed_2499_ = lean_unbox(v_t_2496_);
v_res_2500_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonInst_elim(v_motive_2495_, v_t_boxed_2499_, v_h_2497_, v_canonInst_2498_);
lean_dec(v_canonInst_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim___redArg(lean_object* v_canonImplicit_2501_){
_start:
{
lean_inc(v_canonImplicit_2501_);
return v_canonImplicit_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim___redArg___boxed(lean_object* v_canonImplicit_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim___redArg(v_canonImplicit_2502_);
lean_dec(v_canonImplicit_2502_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim(lean_object* v_motive_2504_, uint8_t v_t_2505_, lean_object* v_h_2506_, lean_object* v_canonImplicit_2507_){
_start:
{
lean_inc(v_canonImplicit_2507_);
return v_canonImplicit_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim___boxed(lean_object* v_motive_2508_, lean_object* v_t_2509_, lean_object* v_h_2510_, lean_object* v_canonImplicit_2511_){
_start:
{
uint8_t v_t_boxed_2512_; lean_object* v_res_2513_; 
v_t_boxed_2512_ = lean_unbox(v_t_2509_);
v_res_2513_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_canonImplicit_elim(v_motive_2508_, v_t_boxed_2512_, v_h_2510_, v_canonImplicit_2511_);
lean_dec(v_canonImplicit_2511_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim___redArg(lean_object* v_visit_2514_){
_start:
{
lean_inc(v_visit_2514_);
return v_visit_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim___redArg___boxed(lean_object* v_visit_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim___redArg(v_visit_2515_);
lean_dec(v_visit_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim(lean_object* v_motive_2517_, uint8_t v_t_2518_, lean_object* v_h_2519_, lean_object* v_visit_2520_){
_start:
{
lean_inc(v_visit_2520_);
return v_visit_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim___boxed(lean_object* v_motive_2521_, lean_object* v_t_2522_, lean_object* v_h_2523_, lean_object* v_visit_2524_){
_start:
{
uint8_t v_t_boxed_2525_; lean_object* v_res_2526_; 
v_t_boxed_2525_ = lean_unbox(v_t_2522_);
v_res_2526_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_ShouldCanonResult_visit_elim(v_motive_2521_, v_t_boxed_2525_, v_h_2523_, v_visit_2524_);
lean_dec(v_visit_2524_);
return v_res_2526_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult_default(void){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = 0;
return v___x_2527_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult(void){
_start:
{
uint8_t v___x_2528_; 
v___x_2528_ = 0;
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0(uint8_t v_r_2541_, lean_object* v_x_2542_){
_start:
{
switch(v_r_2541_)
{
case 0:
{
lean_object* v___x_2543_; 
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__1));
return v___x_2543_;
}
case 1:
{
lean_object* v___x_2544_; 
v___x_2544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__3));
return v___x_2544_;
}
case 2:
{
lean_object* v___x_2545_; 
v___x_2545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__5));
return v___x_2545_;
}
default: 
{
lean_object* v___x_2546_; 
v___x_2546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__7));
return v___x_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___boxed(lean_object* v_r_2547_, lean_object* v_x_2548_){
_start:
{
uint8_t v_r_boxed_2549_; lean_object* v_res_2550_; 
v_r_boxed_2549_ = lean_unbox(v_r_2547_);
v_res_2550_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0(v_r_boxed_2549_, v_x_2548_);
lean_dec(v_x_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon(lean_object* v_pinfos_2553_, lean_object* v_i_2554_, lean_object* v_arg_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = lean_array_get_size(v_pinfos_2553_);
v___x_2612_ = lean_nat_dec_lt(v_i_2554_, v___x_2611_);
if (v___x_2612_ == 0)
{
v___y_2562_ = v_a_2556_;
v___y_2563_ = v_a_2557_;
v___y_2564_ = v_a_2558_;
v___y_2565_ = v_a_2559_;
goto v___jp_2561_;
}
else
{
lean_object* v_pinfo_2613_; uint8_t v_isInstance_2614_; 
v_pinfo_2613_ = lean_array_fget_borrowed(v_pinfos_2553_, v_i_2554_);
v_isInstance_2614_ = lean_ctor_get_uint8(v_pinfo_2613_, sizeof(void*)*1 + 4);
if (v_isInstance_2614_ == 0)
{
uint8_t v_isProp_2615_; 
v_isProp_2615_ = lean_ctor_get_uint8(v_pinfo_2613_, sizeof(void*)*1 + 2);
if (v_isProp_2615_ == 0)
{
uint8_t v___x_2616_; 
v___x_2616_ = l_Lean_Meta_ParamInfo_isImplicit(v_pinfo_2613_);
if (v___x_2616_ == 0)
{
v___y_2562_ = v_a_2556_;
v___y_2563_ = v_a_2557_;
v___y_2564_ = v_a_2558_;
v___y_2565_ = v_a_2559_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_Meta_isTypeFormer(v_arg_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2633_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2633_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2633_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
uint8_t v___x_2622_; 
v___x_2622_ = lean_unbox(v_a_2618_);
lean_dec(v_a_2618_);
if (v___x_2622_ == 0)
{
uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = 2;
v___x_2624_ = lean_box(v___x_2623_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2624_);
v___x_2626_ = v___x_2620_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
else
{
uint8_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2628_ = 0;
v___x_2629_ = lean_box(v___x_2628_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2629_);
v___x_2631_ = v___x_2620_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
v_a_2634_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2617_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2617_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
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
uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec_ref(v_arg_2555_);
v___x_2642_ = 3;
v___x_2643_ = lean_box(v___x_2642_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
else
{
uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec_ref(v_arg_2555_);
v___x_2645_ = 1;
v___x_2646_ = lean_box(v___x_2645_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
}
v___jp_2561_:
{
lean_object* v___x_2566_; 
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc_ref(v___y_2562_);
lean_inc_ref(v_arg_2555_);
v___x_2566_ = l_Lean_Meta_isProp(v_arg_2555_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2602_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2602_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2602_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
uint8_t v___x_2571_; 
v___x_2571_ = lean_unbox(v_a_2567_);
lean_dec(v_a_2567_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_del_object(v___x_2569_);
v___x_2572_ = l_Lean_Meta_isTypeFormer(v_arg_2555_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2588_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2588_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2588_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
uint8_t v___x_2577_; 
v___x_2577_ = lean_unbox(v_a_2573_);
lean_dec(v_a_2573_);
if (v___x_2577_ == 0)
{
uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2578_ = 3;
v___x_2579_ = lean_box(v___x_2578_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2579_);
v___x_2581_ = v___x_2575_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
else
{
uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2583_ = 0;
v___x_2584_ = lean_box(v___x_2583_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2584_);
v___x_2586_ = v___x_2575_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
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
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2572_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2572_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec_ref(v_arg_2555_);
v___x_2597_ = 3;
v___x_2598_ = lean_box(v___x_2597_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2598_);
v___x_2600_ = v___x_2569_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec_ref(v_arg_2555_);
v_a_2603_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2566_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2566_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon___boxed(lean_object* v_pinfos_2648_, lean_object* v_i_2649_, lean_object* v_arg_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon(v_pinfos_2648_, v_i_2649_, v_arg_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_i_2649_);
lean_dec_ref(v_pinfos_2648_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_isSupport(lean_object* v_pinfos_2657_, lean_object* v_i_2658_, lean_object* v_arg_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon(v_pinfos_2657_, v_i_2658_, v_arg_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2681_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2681_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2681_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_unbox(v_a_2666_);
lean_dec(v_a_2666_);
if (v___x_2670_ == 3)
{
uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2671_ = 0;
v___x_2672_ = lean_box(v___x_2671_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2672_);
v___x_2674_ = v___x_2668_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
else
{
uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2676_ = 1;
v___x_2677_ = lean_box(v___x_2676_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2677_);
v___x_2679_ = v___x_2668_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
v_a_2682_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2665_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2665_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_isSupport___boxed(lean_object* v_pinfos_2690_, lean_object* v_i_2691_, lean_object* v_arg_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_Meta_Grind_Canon_isSupport(v_pinfos_2690_, v_i_2691_, v_arg_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_i_2691_);
lean_dec_ref(v_pinfos_2690_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f(lean_object* v_args_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
uint8_t v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2725_; uint8_t v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v_args_2755_; uint8_t v_modified_2756_; lean_object* v___y_2757_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2785_ = lean_array_get_size(v_args_2710_);
v___x_2786_ = lean_unsigned_to_nat(3u);
v___x_2787_ = lean_nat_dec_eq(v___x_2785_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec_ref(v_args_2710_);
goto v___jp_2716_;
}
else
{
uint8_t v_modified_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v_modified_2792_; 
v_modified_2788_ = 0;
v___x_2789_ = lean_unsigned_to_nat(1u);
v___x_2790_ = lean_array_fget_borrowed(v_args_2710_, v___x_2789_);
v___x_2791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__6));
v_modified_2792_ = l_Lean_Expr_isAppOf(v___x_2790_, v___x_2791_);
if (v_modified_2792_ == 0)
{
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec_ref(v_a_2711_);
v_args_2755_ = v_args_2710_;
v_modified_2756_ = v_modified_2788_;
v___y_2757_ = v_a_2712_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2793_; 
lean_inc(v_a_2712_);
v___x_2793_ = l_Lean_Meta_getNatValue_x3f(v___x_2790_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref(v___x_2793_);
if (lean_obj_tag(v_a_2794_) == 1)
{
lean_object* v_val_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_val_2795_ = lean_ctor_get(v_a_2794_, 0);
lean_inc(v_val_2795_);
lean_dec_ref(v_a_2794_);
v___x_2796_ = l_Lean_mkRawNatLit(v_val_2795_);
v___x_2797_ = lean_array_fset(v_args_2710_, v___x_2789_, v___x_2796_);
v_args_2755_ = v___x_2797_;
v_modified_2756_ = v_modified_2792_;
v___y_2757_ = v_a_2712_;
goto v___jp_2754_;
}
else
{
lean_dec(v_a_2794_);
v_args_2755_ = v_args_2710_;
v_modified_2756_ = v_modified_2788_;
v___y_2757_ = v_a_2712_;
goto v___jp_2754_;
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v_a_2712_);
lean_dec_ref(v_args_2710_);
v_a_2798_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2793_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2793_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
v___jp_2716_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_box(0);
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
return v___x_2718_;
}
v___jp_2719_:
{
if (v___y_2720_ == 0)
{
lean_dec_ref(v___y_2721_);
goto v___jp_2716_;
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___y_2721_);
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
v___jp_2724_:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v___y_2728_, v___y_2725_);
lean_dec(v___y_2725_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2745_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2745_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2745_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
uint8_t v___x_2734_; 
v___x_2734_ = lean_unbox(v_a_2730_);
lean_dec(v_a_2730_);
if (v___x_2734_ == 0)
{
lean_del_object(v___x_2732_);
v___y_2720_ = v___y_2726_;
v___y_2721_ = v___y_2727_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = lean_array_fget_borrowed(v___y_2727_, v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__1));
v___x_2738_ = l_Lean_Expr_isConstOf(v___x_2736_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2739_ = l_Lean_Int_mkType;
v___x_2740_ = lean_array_fset(v___y_2727_, v___x_2735_, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2741_);
v___x_2743_ = v___x_2732_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
else
{
lean_del_object(v___x_2732_);
v___y_2720_ = v___y_2726_;
v___y_2721_ = v___y_2727_;
goto v___jp_2719_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v___y_2727_);
v_a_2746_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2729_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2729_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
v___jp_2754_:
{
lean_object* v___x_2758_; lean_object* v_inst_2759_; lean_object* v___x_2760_; 
v___x_2758_ = lean_unsigned_to_nat(2u);
v_inst_2759_ = lean_array_fget_borrowed(v_args_2755_, v___x_2758_);
lean_inc(v_inst_2759_);
v___x_2760_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_inst_2759_, v___y_2757_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2776_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2763_ = v___x_2760_;
v_isShared_2764_ = v_isSharedCheck_2776_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2776_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_unbox(v_a_2761_);
lean_dec(v_a_2761_);
if (v___x_2765_ == 0)
{
lean_inc(v_inst_2759_);
lean_del_object(v___x_2763_);
v___y_2725_ = v___y_2757_;
v___y_2726_ = v_modified_2756_;
v___y_2727_ = v_args_2755_;
v___y_2728_ = v_inst_2759_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = lean_array_fget_borrowed(v_args_2755_, v___x_2766_);
v___x_2768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__3));
v___x_2769_ = l_Lean_Expr_isConstOf(v___x_2767_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v___y_2757_);
v___x_2770_ = l_Lean_Nat_mkType;
v___x_2771_ = lean_array_fset(v_args_2755_, v___x_2766_, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2772_);
v___x_2774_ = v___x_2763_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
else
{
lean_inc(v_inst_2759_);
lean_del_object(v___x_2763_);
v___y_2725_ = v___y_2757_;
v___y_2726_ = v_modified_2756_;
v___y_2727_ = v_args_2755_;
v___y_2728_ = v_inst_2759_;
goto v___jp_2724_;
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v___y_2757_);
lean_dec_ref(v_args_2755_);
v_a_2777_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2760_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2760_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___boxed(lean_object* v_args_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f(v_args_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(lean_object* v_cls_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_options_2816_; uint8_t v_hasTrace_2817_; 
v_options_2816_ = lean_ctor_get(v___y_2814_, 2);
v_hasTrace_2817_ = lean_ctor_get_uint8(v_options_2816_, sizeof(void*)*1);
if (v_hasTrace_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec(v_cls_2813_);
v___x_2818_ = lean_box(v_hasTrace_2817_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
else
{
lean_object* v_inheritedTraceOptions_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_inheritedTraceOptions_2820_ = lean_ctor_get(v___y_2814_, 13);
v___x_2821_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg___closed__1));
v___x_2822_ = l_Lean_Name_append(v___x_2821_, v_cls_2813_);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2820_, v_options_2816_, v___x_2822_);
lean_dec(v___x_2822_);
v___x_2824_ = lean_box(v___x_2823_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg___boxed(lean_object* v_cls_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(v_cls_2826_, v___y_2827_);
lean_dec_ref(v___y_2827_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2(lean_object* v_cls_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(v_cls_2830_, v___y_2840_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___boxed(lean_object* v_cls_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2(v_cls_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
return v_res_2857_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__0(void){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7(lean_object* v_msg_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v_toApplicative_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2946_; 
v___x_2876_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__0);
v___x_2877_ = l_ReaderT_instMonad___redArg(v___x_2876_);
v_toApplicative_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; 
v_unused_2947_ = lean_ctor_get(v___x_2877_, 1);
lean_dec(v_unused_2947_);
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2946_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_toApplicative_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2946_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v_toFunctor_2882_; lean_object* v_toSeq_2883_; lean_object* v_toSeqLeft_2884_; lean_object* v_toSeqRight_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2944_; 
v_toFunctor_2882_ = lean_ctor_get(v_toApplicative_2878_, 0);
v_toSeq_2883_ = lean_ctor_get(v_toApplicative_2878_, 2);
v_toSeqLeft_2884_ = lean_ctor_get(v_toApplicative_2878_, 3);
v_toSeqRight_2885_ = lean_ctor_get(v_toApplicative_2878_, 4);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_toApplicative_2878_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v_toApplicative_2878_, 1);
lean_dec(v_unused_2945_);
v___x_2887_ = v_toApplicative_2878_;
v_isShared_2888_ = v_isSharedCheck_2944_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_toSeqRight_2885_);
lean_inc(v_toSeqLeft_2884_);
lean_inc(v_toSeq_2883_);
lean_inc(v_toFunctor_2882_);
lean_dec(v_toApplicative_2878_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2944_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___f_2889_; lean_object* v___f_2890_; lean_object* v___f_2891_; lean_object* v___f_2892_; lean_object* v___x_2893_; lean_object* v___f_2894_; lean_object* v___f_2895_; lean_object* v___f_2896_; lean_object* v___x_2898_; 
v___f_2889_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__1));
v___f_2890_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__2));
lean_inc_ref(v_toFunctor_2882_);
v___f_2891_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2891_, 0, v_toFunctor_2882_);
v___f_2892_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2892_, 0, v_toFunctor_2882_);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___f_2891_);
lean_ctor_set(v___x_2893_, 1, v___f_2892_);
v___f_2894_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2894_, 0, v_toSeqRight_2885_);
v___f_2895_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2895_, 0, v_toSeqLeft_2884_);
v___f_2896_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2896_, 0, v_toSeq_2883_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 4, v___f_2894_);
lean_ctor_set(v___x_2887_, 3, v___f_2895_);
lean_ctor_set(v___x_2887_, 2, v___f_2896_);
lean_ctor_set(v___x_2887_, 1, v___f_2889_);
lean_ctor_set(v___x_2887_, 0, v___x_2893_);
v___x_2898_ = v___x_2887_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___f_2889_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v___f_2896_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v___f_2895_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v___f_2894_);
v___x_2898_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 1, v___f_2890_);
lean_ctor_set(v___x_2880_, 0, v___x_2898_);
v___x_2900_ = v___x_2880_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v___f_2890_);
v___x_2900_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v_toApplicative_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2940_; 
v___x_2901_ = l_ReaderT_instMonad___redArg(v___x_2900_);
v_toApplicative_2902_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2940_ == 0)
{
lean_object* v_unused_2941_; 
v_unused_2941_ = lean_ctor_get(v___x_2901_, 1);
lean_dec(v_unused_2941_);
v___x_2904_ = v___x_2901_;
v_isShared_2905_ = v_isSharedCheck_2940_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_toApplicative_2902_);
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2940_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v_toFunctor_2906_; lean_object* v_toSeq_2907_; lean_object* v_toSeqLeft_2908_; lean_object* v_toSeqRight_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2938_; 
v_toFunctor_2906_ = lean_ctor_get(v_toApplicative_2902_, 0);
v_toSeq_2907_ = lean_ctor_get(v_toApplicative_2902_, 2);
v_toSeqLeft_2908_ = lean_ctor_get(v_toApplicative_2902_, 3);
v_toSeqRight_2909_ = lean_ctor_get(v_toApplicative_2902_, 4);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_toApplicative_2902_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v_toApplicative_2902_, 1);
lean_dec(v_unused_2939_);
v___x_2911_ = v_toApplicative_2902_;
v_isShared_2912_ = v_isSharedCheck_2938_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_toSeqRight_2909_);
lean_inc(v_toSeqLeft_2908_);
lean_inc(v_toSeq_2907_);
lean_inc(v_toFunctor_2906_);
lean_dec(v_toApplicative_2902_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2938_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___f_2913_; lean_object* v___f_2914_; lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; lean_object* v___f_2918_; lean_object* v___f_2919_; lean_object* v___f_2920_; lean_object* v___x_2922_; 
v___f_2913_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__3));
v___f_2914_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___closed__4));
lean_inc_ref(v_toFunctor_2906_);
v___f_2915_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2915_, 0, v_toFunctor_2906_);
v___f_2916_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2916_, 0, v_toFunctor_2906_);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___f_2915_);
lean_ctor_set(v___x_2917_, 1, v___f_2916_);
v___f_2918_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2918_, 0, v_toSeqRight_2909_);
v___f_2919_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2919_, 0, v_toSeqLeft_2908_);
v___f_2920_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2920_, 0, v_toSeq_2907_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 4, v___f_2918_);
lean_ctor_set(v___x_2911_, 3, v___f_2919_);
lean_ctor_set(v___x_2911_, 2, v___f_2920_);
lean_ctor_set(v___x_2911_, 1, v___f_2913_);
lean_ctor_set(v___x_2911_, 0, v___x_2917_);
v___x_2922_ = v___x_2911_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___f_2913_);
lean_ctor_set(v_reuseFailAlloc_2937_, 2, v___f_2920_);
lean_ctor_set(v_reuseFailAlloc_2937_, 3, v___f_2919_);
lean_ctor_set(v_reuseFailAlloc_2937_, 4, v___f_2918_);
v___x_2922_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 1, v___f_2914_);
lean_ctor_set(v___x_2904_, 0, v___x_2922_);
v___x_2924_ = v___x_2904_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2922_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v___f_2914_);
v___x_2924_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_144192__overap_2934_; lean_object* v___x_2935_; 
v___x_2925_ = l_ReaderT_instMonad___redArg(v___x_2924_);
v___x_2926_ = l_ReaderT_instMonad___redArg(v___x_2925_);
v___x_2927_ = l_ReaderT_instMonad___redArg(v___x_2926_);
v___x_2928_ = l_ReaderT_instMonad___redArg(v___x_2927_);
v___x_2929_ = l_ReaderT_instMonad___redArg(v___x_2928_);
v___x_2930_ = l_ReaderT_instMonad___redArg(v___x_2929_);
v___x_2931_ = l_ReaderT_instMonad___redArg(v___x_2930_);
v___x_2932_ = l_Lean_instInhabitedExpr;
v___x_2933_ = l_instInhabitedOfMonad___redArg(v___x_2931_, v___x_2932_);
v___x_144192__overap_2934_ = lean_panic_fn(v___x_2933_, v_msg_2863_);
v___x_2935_ = lean_apply_12(v___x_144192__overap_2934_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, lean_box(0));
return v___x_2935_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7___boxed(lean_object* v_msg_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7(v_msg_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___redArg(lean_object* v_keys_2962_, lean_object* v_vals_2963_, lean_object* v_i_2964_, lean_object* v_k_2965_){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = lean_array_get_size(v_keys_2962_);
v___x_2967_ = lean_nat_dec_lt(v_i_2964_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
lean_dec(v_i_2964_);
v___x_2968_ = lean_box(0);
return v___x_2968_;
}
else
{
lean_object* v_k_x27_2969_; uint8_t v___x_2970_; 
v_k_x27_2969_ = lean_array_fget_borrowed(v_keys_2962_, v_i_2964_);
v___x_2970_ = lean_expr_eqv(v_k_2965_, v_k_x27_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_unsigned_to_nat(1u);
v___x_2972_ = lean_nat_add(v_i_2964_, v___x_2971_);
lean_dec(v_i_2964_);
v_i_2964_ = v___x_2972_;
goto _start;
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = lean_array_fget_borrowed(v_vals_2963_, v_i_2964_);
lean_dec(v_i_2964_);
lean_inc(v___x_2974_);
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_keys_2976_, lean_object* v_vals_2977_, lean_object* v_i_2978_, lean_object* v_k_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___redArg(v_keys_2976_, v_vals_2977_, v_i_2978_, v_k_2979_);
lean_dec_ref(v_k_2979_);
lean_dec_ref(v_vals_2977_);
lean_dec_ref(v_keys_2976_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___redArg(lean_object* v_x_2981_, size_t v_x_2982_, lean_object* v_x_2983_){
_start:
{
if (lean_obj_tag(v_x_2981_) == 0)
{
lean_object* v_es_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3005_; 
v_es_2984_ = lean_ctor_get(v_x_2981_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_x_2981_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2986_ = v_x_2981_;
v_isShared_2987_ = v_isSharedCheck_3005_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_es_2984_);
lean_dec(v_x_2981_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3005_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; size_t v___x_2989_; size_t v___x_2990_; size_t v___x_2991_; lean_object* v_j_2992_; lean_object* v___x_2993_; 
v___x_2988_ = lean_box(2);
v___x_2989_ = ((size_t)5ULL);
v___x_2990_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0_spec__0___redArg___closed__1);
v___x_2991_ = lean_usize_land(v_x_2982_, v___x_2990_);
v_j_2992_ = lean_usize_to_nat(v___x_2991_);
v___x_2993_ = lean_array_get(v___x_2988_, v_es_2984_, v_j_2992_);
lean_dec(v_j_2992_);
lean_dec_ref(v_es_2984_);
switch(lean_obj_tag(v___x_2993_))
{
case 0:
{
lean_object* v_key_2994_; lean_object* v_val_2995_; uint8_t v___x_2996_; 
v_key_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_key_2994_);
v_val_2995_ = lean_ctor_get(v___x_2993_, 1);
lean_inc(v_val_2995_);
lean_dec_ref(v___x_2993_);
v___x_2996_ = lean_expr_eqv(v_x_2983_, v_key_2994_);
lean_dec(v_key_2994_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; 
lean_dec(v_val_2995_);
lean_del_object(v___x_2986_);
v___x_2997_ = lean_box(0);
return v___x_2997_;
}
else
{
lean_object* v___x_2999_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 1);
lean_ctor_set(v___x_2986_, 0, v_val_2995_);
v___x_2999_ = v___x_2986_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_val_2995_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
case 1:
{
lean_object* v_node_3001_; size_t v___x_3002_; 
lean_del_object(v___x_2986_);
v_node_3001_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_node_3001_);
lean_dec_ref(v___x_2993_);
v___x_3002_ = lean_usize_shift_right(v_x_2982_, v___x_2989_);
v_x_2981_ = v_node_3001_;
v_x_2982_ = v___x_3002_;
goto _start;
}
default: 
{
lean_object* v___x_3004_; 
lean_del_object(v___x_2986_);
v___x_3004_ = lean_box(0);
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_ks_3006_; lean_object* v_vs_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_ks_3006_ = lean_ctor_get(v_x_2981_, 0);
lean_inc_ref(v_ks_3006_);
v_vs_3007_ = lean_ctor_get(v_x_2981_, 1);
lean_inc_ref(v_vs_3007_);
lean_dec_ref(v_x_2981_);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___redArg(v_ks_3006_, v_vs_3007_, v___x_3008_, v_x_2983_);
lean_dec_ref(v_vs_3007_);
lean_dec_ref(v_ks_3006_);
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___redArg___boxed(lean_object* v_x_3010_, lean_object* v_x_3011_, lean_object* v_x_3012_){
_start:
{
size_t v_x_145551__boxed_3013_; lean_object* v_res_3014_; 
v_x_145551__boxed_3013_ = lean_unbox_usize(v_x_3011_);
lean_dec(v_x_3011_);
v_res_3014_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___redArg(v_x_3010_, v_x_145551__boxed_3013_, v_x_3012_);
lean_dec_ref(v_x_3012_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(lean_object* v_x_3015_, lean_object* v_x_3016_){
_start:
{
uint64_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = l_Lean_Expr_hash(v_x_3016_);
v___x_3018_ = lean_uint64_to_usize(v___x_3017_);
v___x_3019_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___redArg(v_x_3015_, v___x_3018_, v_x_3016_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg___boxed(lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(v_x_3020_, v_x_3021_);
lean_dec_ref(v_x_3021_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(lean_object* v_cls_3023_, lean_object* v_msg_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_ref_3030_; lean_object* v___x_3031_; lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3076_; 
v_ref_3030_ = lean_ctor_get(v___y_3027_, 5);
v___x_3031_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2_spec__3(v_msg_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3076_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3076_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v_traceState_3037_; lean_object* v_env_3038_; lean_object* v_nextMacroScope_3039_; lean_object* v_ngen_3040_; lean_object* v_auxDeclNGen_3041_; lean_object* v_cache_3042_; lean_object* v_messages_3043_; lean_object* v_infoState_3044_; lean_object* v_snapshotTasks_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3075_; 
v___x_3036_ = lean_st_ref_take(v___y_3028_);
v_traceState_3037_ = lean_ctor_get(v___x_3036_, 4);
v_env_3038_ = lean_ctor_get(v___x_3036_, 0);
v_nextMacroScope_3039_ = lean_ctor_get(v___x_3036_, 1);
v_ngen_3040_ = lean_ctor_get(v___x_3036_, 2);
v_auxDeclNGen_3041_ = lean_ctor_get(v___x_3036_, 3);
v_cache_3042_ = lean_ctor_get(v___x_3036_, 5);
v_messages_3043_ = lean_ctor_get(v___x_3036_, 6);
v_infoState_3044_ = lean_ctor_get(v___x_3036_, 7);
v_snapshotTasks_3045_ = lean_ctor_get(v___x_3036_, 8);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3047_ = v___x_3036_;
v_isShared_3048_ = v_isSharedCheck_3075_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_snapshotTasks_3045_);
lean_inc(v_infoState_3044_);
lean_inc(v_messages_3043_);
lean_inc(v_cache_3042_);
lean_inc(v_traceState_3037_);
lean_inc(v_auxDeclNGen_3041_);
lean_inc(v_ngen_3040_);
lean_inc(v_nextMacroScope_3039_);
lean_inc(v_env_3038_);
lean_dec(v___x_3036_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3075_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
uint64_t v_tid_3049_; lean_object* v_traces_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3074_; 
v_tid_3049_ = lean_ctor_get_uint64(v_traceState_3037_, sizeof(void*)*1);
v_traces_3050_ = lean_ctor_get(v_traceState_3037_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_traceState_3037_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3052_ = v_traceState_3037_;
v_isShared_3053_ = v_isSharedCheck_3074_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_traces_3050_);
lean_dec(v_traceState_3037_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3074_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; double v___x_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__0);
v___x_3056_ = 0;
v___x_3057_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__1));
v___x_3058_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3058_, 0, v_cls_3023_);
lean_ctor_set(v___x_3058_, 1, v___x_3054_);
lean_ctor_set(v___x_3058_, 2, v___x_3057_);
lean_ctor_set_float(v___x_3058_, sizeof(void*)*3, v___x_3055_);
lean_ctor_set_float(v___x_3058_, sizeof(void*)*3 + 8, v___x_3055_);
lean_ctor_set_uint8(v___x_3058_, sizeof(void*)*3 + 16, v___x_3056_);
v___x_3059_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg___closed__2));
v___x_3060_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v_a_3032_);
lean_ctor_set(v___x_3060_, 2, v___x_3059_);
lean_inc(v_ref_3030_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v_ref_3030_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = l_Lean_PersistentArray_push___redArg(v_traces_3050_, v___x_3061_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3062_);
v___x_3064_ = v___x_3052_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3062_);
lean_ctor_set_uint64(v_reuseFailAlloc_3073_, sizeof(void*)*1, v_tid_3049_);
v___x_3064_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 4, v___x_3064_);
v___x_3066_ = v___x_3047_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_env_3038_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_nextMacroScope_3039_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_ngen_3040_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_auxDeclNGen_3041_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3072_, 5, v_cache_3042_);
lean_ctor_set(v_reuseFailAlloc_3072_, 6, v_messages_3043_);
lean_ctor_set(v_reuseFailAlloc_3072_, 7, v_infoState_3044_);
lean_ctor_set(v_reuseFailAlloc_3072_, 8, v_snapshotTasks_3045_);
v___x_3066_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3067_ = lean_st_ref_set(v___y_3028_, v___x_3066_);
v___x_3068_ = lean_box(0);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3068_);
v___x_3070_ = v___x_3034_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg___boxed(lean_object* v_cls_3077_, lean_object* v_msg_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(v_cls_3077_, v_msg_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3084_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___lam__0(lean_object* v_x_3085_, lean_object* v_00___3086_){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3087_ = lean_array_get_size(v_x_3085_);
v___x_3088_ = lean_unsigned_to_nat(2u);
v___x_3089_ = lean_nat_dec_eq(v___x_3087_, v___x_3088_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___lam__0___boxed(lean_object* v_x_3090_, lean_object* v_00___3091_){
_start:
{
uint8_t v_res_3092_; lean_object* v_r_3093_; 
v_res_3092_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___lam__0(v_x_3090_, v_00___3091_);
lean_dec_ref(v_x_3090_);
v_r_3093_ = lean_box(v_res_3092_);
return v_r_3093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___redArg(lean_object* v_a_3094_, lean_object* v_x_3095_){
_start:
{
if (lean_obj_tag(v_x_3095_) == 0)
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_box(0);
return v___x_3096_;
}
else
{
lean_object* v_key_3097_; lean_object* v_value_3098_; lean_object* v_tail_3099_; uint8_t v___x_3100_; 
v_key_3097_ = lean_ctor_get(v_x_3095_, 0);
v_value_3098_ = lean_ctor_get(v_x_3095_, 1);
v_tail_3099_ = lean_ctor_get(v_x_3095_, 2);
v___x_3100_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_3097_, v_a_3094_);
if (v___x_3100_ == 0)
{
v_x_3095_ = v_tail_3099_;
goto _start;
}
else
{
lean_object* v___x_3102_; 
lean_inc(v_value_3098_);
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_value_3098_);
return v___x_3102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___redArg___boxed(lean_object* v_a_3103_, lean_object* v_x_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___redArg(v_a_3103_, v_x_3104_);
lean_dec(v_x_3104_);
lean_dec_ref(v_a_3103_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(lean_object* v_m_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_buckets_3108_; lean_object* v___x_3109_; uint64_t v___x_3110_; uint64_t v___x_3111_; uint64_t v___x_3112_; uint64_t v_fold_3113_; uint64_t v___x_3114_; uint64_t v___x_3115_; uint64_t v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_buckets_3108_ = lean_ctor_get(v_m_3106_, 1);
v___x_3109_ = lean_array_get_size(v_buckets_3108_);
v___x_3110_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_3107_);
v___x_3111_ = 32ULL;
v___x_3112_ = lean_uint64_shift_right(v___x_3110_, v___x_3111_);
v_fold_3113_ = lean_uint64_xor(v___x_3110_, v___x_3112_);
v___x_3114_ = 16ULL;
v___x_3115_ = lean_uint64_shift_right(v_fold_3113_, v___x_3114_);
v___x_3116_ = lean_uint64_xor(v_fold_3113_, v___x_3115_);
v___x_3117_ = lean_uint64_to_usize(v___x_3116_);
v___x_3118_ = lean_usize_of_nat(v___x_3109_);
v___x_3119_ = ((size_t)1ULL);
v___x_3120_ = lean_usize_sub(v___x_3118_, v___x_3119_);
v___x_3121_ = lean_usize_land(v___x_3117_, v___x_3120_);
v___x_3122_ = lean_array_uget_borrowed(v_buckets_3108_, v___x_3121_);
v___x_3123_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___redArg(v_a_3107_, v___x_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg___boxed(lean_object* v_m_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(v_m_3124_, v_a_3125_);
lean_dec_ref(v_a_3125_);
lean_dec_ref(v_m_3124_);
return v_res_3126_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___redArg(lean_object* v_a_3127_, lean_object* v_x_3128_){
_start:
{
if (lean_obj_tag(v_x_3128_) == 0)
{
uint8_t v___x_3129_; 
v___x_3129_ = 0;
return v___x_3129_;
}
else
{
lean_object* v_key_3130_; lean_object* v_tail_3131_; uint8_t v___x_3132_; 
v_key_3130_ = lean_ctor_get(v_x_3128_, 0);
v_tail_3131_ = lean_ctor_get(v_x_3128_, 2);
v___x_3132_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_3130_, v_a_3127_);
if (v___x_3132_ == 0)
{
v_x_3128_ = v_tail_3131_;
goto _start;
}
else
{
return v___x_3132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_3134_, lean_object* v_x_3135_){
_start:
{
uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_res_3136_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___redArg(v_a_3134_, v_x_3135_);
lean_dec(v_x_3135_);
lean_dec_ref(v_a_3134_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4_spec__10___redArg(lean_object* v_x_3138_, lean_object* v_x_3139_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
return v_x_3138_;
}
else
{
lean_object* v_key_3140_; lean_object* v_value_3141_; lean_object* v_tail_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3165_; 
v_key_3140_ = lean_ctor_get(v_x_3139_, 0);
v_value_3141_ = lean_ctor_get(v_x_3139_, 1);
v_tail_3142_ = lean_ctor_get(v_x_3139_, 2);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_x_3139_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3144_ = v_x_3139_;
v_isShared_3145_ = v_isSharedCheck_3165_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_tail_3142_);
lean_inc(v_value_3141_);
lean_inc(v_key_3140_);
lean_dec(v_x_3139_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3165_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; uint64_t v___x_3147_; uint64_t v___x_3148_; uint64_t v___x_3149_; uint64_t v_fold_3150_; uint64_t v___x_3151_; uint64_t v___x_3152_; uint64_t v___x_3153_; size_t v___x_3154_; size_t v___x_3155_; size_t v___x_3156_; size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3146_ = lean_array_get_size(v_x_3138_);
v___x_3147_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_3140_);
v___x_3148_ = 32ULL;
v___x_3149_ = lean_uint64_shift_right(v___x_3147_, v___x_3148_);
v_fold_3150_ = lean_uint64_xor(v___x_3147_, v___x_3149_);
v___x_3151_ = 16ULL;
v___x_3152_ = lean_uint64_shift_right(v_fold_3150_, v___x_3151_);
v___x_3153_ = lean_uint64_xor(v_fold_3150_, v___x_3152_);
v___x_3154_ = lean_uint64_to_usize(v___x_3153_);
v___x_3155_ = lean_usize_of_nat(v___x_3146_);
v___x_3156_ = ((size_t)1ULL);
v___x_3157_ = lean_usize_sub(v___x_3155_, v___x_3156_);
v___x_3158_ = lean_usize_land(v___x_3154_, v___x_3157_);
v___x_3159_ = lean_array_uget_borrowed(v_x_3138_, v___x_3158_);
lean_inc(v___x_3159_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 2, v___x_3159_);
v___x_3161_ = v___x_3144_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_key_3140_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_value_3141_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_array_uset(v_x_3138_, v___x_3158_, v___x_3161_);
v_x_3138_ = v___x_3162_;
v_x_3139_ = v_tail_3142_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4___redArg(lean_object* v_i_3166_, lean_object* v_source_3167_, lean_object* v_target_3168_){
_start:
{
lean_object* v___x_3169_; uint8_t v___x_3170_; 
v___x_3169_ = lean_array_get_size(v_source_3167_);
v___x_3170_ = lean_nat_dec_lt(v_i_3166_, v___x_3169_);
if (v___x_3170_ == 0)
{
lean_dec_ref(v_source_3167_);
lean_dec(v_i_3166_);
return v_target_3168_;
}
else
{
lean_object* v_es_3171_; lean_object* v___x_3172_; lean_object* v_source_3173_; lean_object* v_target_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v_es_3171_ = lean_array_fget(v_source_3167_, v_i_3166_);
v___x_3172_ = lean_box(0);
v_source_3173_ = lean_array_fset(v_source_3167_, v_i_3166_, v___x_3172_);
v_target_3174_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4_spec__10___redArg(v_target_3168_, v_es_3171_);
v___x_3175_ = lean_unsigned_to_nat(1u);
v___x_3176_ = lean_nat_add(v_i_3166_, v___x_3175_);
lean_dec(v_i_3166_);
v_i_3166_ = v___x_3176_;
v_source_3167_ = v_source_3173_;
v_target_3168_ = v_target_3174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1___redArg(lean_object* v_data_3178_){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v_nbuckets_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3179_ = lean_array_get_size(v_data_3178_);
v___x_3180_ = lean_unsigned_to_nat(2u);
v_nbuckets_3181_ = lean_nat_mul(v___x_3179_, v___x_3180_);
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_box(0);
v___x_3184_ = lean_mk_array(v_nbuckets_3181_, v___x_3183_);
v___x_3185_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4___redArg(v___x_3182_, v_data_3178_, v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__2___redArg(lean_object* v_a_3186_, lean_object* v_b_3187_, lean_object* v_x_3188_){
_start:
{
if (lean_obj_tag(v_x_3188_) == 0)
{
lean_dec(v_b_3187_);
lean_dec_ref(v_a_3186_);
return v_x_3188_;
}
else
{
lean_object* v_key_3189_; lean_object* v_value_3190_; lean_object* v_tail_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3203_; 
v_key_3189_ = lean_ctor_get(v_x_3188_, 0);
v_value_3190_ = lean_ctor_get(v_x_3188_, 1);
v_tail_3191_ = lean_ctor_get(v_x_3188_, 2);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_x_3188_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3193_ = v_x_3188_;
v_isShared_3194_ = v_isSharedCheck_3203_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_tail_3191_);
lean_inc(v_value_3190_);
lean_inc(v_key_3189_);
lean_dec(v_x_3188_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3203_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
uint8_t v___x_3195_; 
v___x_3195_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_3189_, v_a_3186_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3196_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__2___redArg(v_a_3186_, v_b_3187_, v_tail_3191_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 2, v___x_3196_);
v___x_3198_ = v___x_3193_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_key_3189_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_value_3190_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
else
{
lean_object* v___x_3201_; 
lean_dec(v_value_3190_);
lean_dec(v_key_3189_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 1, v_b_3187_);
lean_ctor_set(v___x_3193_, 0, v_a_3186_);
v___x_3201_ = v___x_3193_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3186_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_b_3187_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_tail_3191_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(lean_object* v_m_3204_, lean_object* v_a_3205_, lean_object* v_b_3206_){
_start:
{
lean_object* v_size_3207_; lean_object* v_buckets_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3251_; 
v_size_3207_ = lean_ctor_get(v_m_3204_, 0);
v_buckets_3208_ = lean_ctor_get(v_m_3204_, 1);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_m_3204_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3210_ = v_m_3204_;
v_isShared_3211_ = v_isSharedCheck_3251_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_buckets_3208_);
lean_inc(v_size_3207_);
lean_dec(v_m_3204_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3251_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; uint64_t v___x_3213_; uint64_t v___x_3214_; uint64_t v___x_3215_; uint64_t v_fold_3216_; uint64_t v___x_3217_; uint64_t v___x_3218_; uint64_t v___x_3219_; size_t v___x_3220_; size_t v___x_3221_; size_t v___x_3222_; size_t v___x_3223_; size_t v___x_3224_; lean_object* v_bkt_3225_; uint8_t v___x_3226_; 
v___x_3212_ = lean_array_get_size(v_buckets_3208_);
v___x_3213_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_3205_);
v___x_3214_ = 32ULL;
v___x_3215_ = lean_uint64_shift_right(v___x_3213_, v___x_3214_);
v_fold_3216_ = lean_uint64_xor(v___x_3213_, v___x_3215_);
v___x_3217_ = 16ULL;
v___x_3218_ = lean_uint64_shift_right(v_fold_3216_, v___x_3217_);
v___x_3219_ = lean_uint64_xor(v_fold_3216_, v___x_3218_);
v___x_3220_ = lean_uint64_to_usize(v___x_3219_);
v___x_3221_ = lean_usize_of_nat(v___x_3212_);
v___x_3222_ = ((size_t)1ULL);
v___x_3223_ = lean_usize_sub(v___x_3221_, v___x_3222_);
v___x_3224_ = lean_usize_land(v___x_3220_, v___x_3223_);
v_bkt_3225_ = lean_array_uget_borrowed(v_buckets_3208_, v___x_3224_);
v___x_3226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___redArg(v_a_3205_, v_bkt_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v_size_x27_3228_; lean_object* v___x_3229_; lean_object* v_buckets_x27_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3227_ = lean_unsigned_to_nat(1u);
v_size_x27_3228_ = lean_nat_add(v_size_3207_, v___x_3227_);
lean_dec(v_size_3207_);
lean_inc(v_bkt_3225_);
v___x_3229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3229_, 0, v_a_3205_);
lean_ctor_set(v___x_3229_, 1, v_b_3206_);
lean_ctor_set(v___x_3229_, 2, v_bkt_3225_);
v_buckets_x27_3230_ = lean_array_uset(v_buckets_3208_, v___x_3224_, v___x_3229_);
v___x_3231_ = lean_unsigned_to_nat(4u);
v___x_3232_ = lean_nat_mul(v_size_x27_3228_, v___x_3231_);
v___x_3233_ = lean_unsigned_to_nat(3u);
v___x_3234_ = lean_nat_div(v___x_3232_, v___x_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_array_get_size(v_buckets_x27_3230_);
v___x_3236_ = lean_nat_dec_le(v___x_3234_, v___x_3235_);
lean_dec(v___x_3234_);
if (v___x_3236_ == 0)
{
lean_object* v_val_3237_; lean_object* v___x_3239_; 
v_val_3237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1___redArg(v_buckets_x27_3230_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v_val_3237_);
lean_ctor_set(v___x_3210_, 0, v_size_x27_3228_);
v___x_3239_ = v___x_3210_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_size_x27_3228_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_val_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
else
{
lean_object* v___x_3242_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v_buckets_x27_3230_);
lean_ctor_set(v___x_3210_, 0, v_size_x27_3228_);
v___x_3242_ = v___x_3210_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_size_x27_3228_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_buckets_x27_3230_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
else
{
lean_object* v___x_3244_; lean_object* v_buckets_x27_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
lean_inc(v_bkt_3225_);
v___x_3244_ = lean_box(0);
v_buckets_x27_3245_ = lean_array_uset(v_buckets_3208_, v___x_3224_, v___x_3244_);
v___x_3246_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__2___redArg(v_a_3205_, v_b_3206_, v_bkt_3225_);
v___x_3247_ = lean_array_uset(v_buckets_x27_3245_, v___x_3224_, v___x_3246_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3247_);
v___x_3249_ = v___x_3210_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_size_3207_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__0(void){
_start:
{
lean_object* v___x_3252_; lean_object* v_dummy_3253_; 
v___x_3252_ = lean_box(0);
v_dummy_3253_ = l_Lean_Expr_sort___override(v___x_3252_);
return v_dummy_3253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__4(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__3));
v___x_3258_ = lean_unsigned_to_nat(13u);
v___x_3259_ = lean_unsigned_to_nat(307u);
v___x_3260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__2));
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__1));
v___x_3262_ = l_mkPanicMessageWithDecl(v___x_3261_, v___x_3260_, v___x_3259_, v___x_3258_, v___x_3257_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___lam__0(lean_object* v___x_3270_, lean_object* v_a_3271_, lean_object* v___x_3272_, lean_object* v_snd_3273_, uint8_t v___y_3274_, lean_object* v_fst_3275_, lean_object* v_e_3276_, lean_object* v_f_3277_, uint8_t v___y_3278_, lean_object* v___x_3279_, lean_object* v_____r_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_arg_x27_3294_; lean_object* v___x_3304_; 
lean_inc(v___y_3291_);
lean_inc_ref(v___y_3290_);
lean_inc(v___y_3289_);
lean_inc_ref(v___y_3288_);
lean_inc_ref(v___x_3272_);
v___x_3304_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon(v___x_3270_, v_a_3271_, v___x_3272_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; uint8_t v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref(v___x_3304_);
v___x_3306_ = lean_unbox(v_a_3305_);
lean_dec(v_a_3305_);
switch(v___x_3306_)
{
case 0:
{
lean_object* v___x_3307_; 
lean_inc(v___y_3291_);
lean_inc_ref(v___y_3290_);
lean_inc(v___y_3289_);
lean_inc_ref(v___y_3288_);
lean_inc(v___y_3287_);
lean_inc_ref(v___y_3286_);
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc(v___y_3283_);
lean_inc(v___y_3282_);
lean_inc_ref(v___x_3272_);
v___x_3307_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v___x_3272_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3309_; uint8_t v_foApprox_3310_; uint8_t v_ctxApprox_3311_; uint8_t v_quasiPatternApprox_3312_; uint8_t v_constApprox_3313_; uint8_t v_isDefEqStuckEx_3314_; uint8_t v_unificationHints_3315_; uint8_t v_proofIrrelevance_3316_; uint8_t v_assignSyntheticOpaque_3317_; uint8_t v_offsetCnstrs_3318_; uint8_t v_etaStruct_3319_; uint8_t v_univApprox_3320_; uint8_t v_iota_3321_; uint8_t v_beta_3322_; uint8_t v_proj_3323_; uint8_t v_zeta_3324_; uint8_t v_zetaDelta_3325_; uint8_t v_zetaUnused_3326_; uint8_t v_zetaHave_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3377_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = l_Lean_Meta_Context_config(v___y_3288_);
v_foApprox_3310_ = lean_ctor_get_uint8(v___x_3309_, 0);
v_ctxApprox_3311_ = lean_ctor_get_uint8(v___x_3309_, 1);
v_quasiPatternApprox_3312_ = lean_ctor_get_uint8(v___x_3309_, 2);
v_constApprox_3313_ = lean_ctor_get_uint8(v___x_3309_, 3);
v_isDefEqStuckEx_3314_ = lean_ctor_get_uint8(v___x_3309_, 4);
v_unificationHints_3315_ = lean_ctor_get_uint8(v___x_3309_, 5);
v_proofIrrelevance_3316_ = lean_ctor_get_uint8(v___x_3309_, 6);
v_assignSyntheticOpaque_3317_ = lean_ctor_get_uint8(v___x_3309_, 7);
v_offsetCnstrs_3318_ = lean_ctor_get_uint8(v___x_3309_, 8);
v_etaStruct_3319_ = lean_ctor_get_uint8(v___x_3309_, 10);
v_univApprox_3320_ = lean_ctor_get_uint8(v___x_3309_, 11);
v_iota_3321_ = lean_ctor_get_uint8(v___x_3309_, 12);
v_beta_3322_ = lean_ctor_get_uint8(v___x_3309_, 13);
v_proj_3323_ = lean_ctor_get_uint8(v___x_3309_, 14);
v_zeta_3324_ = lean_ctor_get_uint8(v___x_3309_, 15);
v_zetaDelta_3325_ = lean_ctor_get_uint8(v___x_3309_, 16);
v_zetaUnused_3326_ = lean_ctor_get_uint8(v___x_3309_, 17);
v_zetaHave_3327_ = lean_ctor_get_uint8(v___x_3309_, 18);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3329_ = v___x_3309_;
v_isShared_3330_ = v_isSharedCheck_3377_;
goto v_resetjp_3328_;
}
else
{
lean_dec(v___x_3309_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3377_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
uint8_t v_trackZetaDelta_3331_; lean_object* v_zetaDeltaSet_3332_; lean_object* v_lctx_3333_; lean_object* v_localInstances_3334_; lean_object* v_defEqCtx_x3f_3335_; lean_object* v_synthPendingDepth_3336_; lean_object* v_canUnfold_x3f_3337_; uint8_t v_univApprox_3338_; uint8_t v_inTypeClassResolution_3339_; uint8_t v_cacheInferType_3340_; uint8_t v___x_3341_; lean_object* v_config_3343_; 
v_trackZetaDelta_3331_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7);
v_zetaDeltaSet_3332_ = lean_ctor_get(v___y_3288_, 1);
lean_inc(v_zetaDeltaSet_3332_);
v_lctx_3333_ = lean_ctor_get(v___y_3288_, 2);
lean_inc_ref(v_lctx_3333_);
v_localInstances_3334_ = lean_ctor_get(v___y_3288_, 3);
lean_inc_ref(v_localInstances_3334_);
v_defEqCtx_x3f_3335_ = lean_ctor_get(v___y_3288_, 4);
lean_inc(v_defEqCtx_x3f_3335_);
v_synthPendingDepth_3336_ = lean_ctor_get(v___y_3288_, 5);
lean_inc(v_synthPendingDepth_3336_);
v_canUnfold_x3f_3337_ = lean_ctor_get(v___y_3288_, 6);
lean_inc(v_canUnfold_x3f_3337_);
v_univApprox_3338_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3339_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 2);
v_cacheInferType_3340_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 3);
v___x_3341_ = 1;
if (v_isShared_3330_ == 0)
{
v_config_3343_ = v___x_3329_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 0, v_foApprox_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 1, v_ctxApprox_3311_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 2, v_quasiPatternApprox_3312_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 3, v_constApprox_3313_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 4, v_isDefEqStuckEx_3314_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 5, v_unificationHints_3315_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 6, v_proofIrrelevance_3316_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 7, v_assignSyntheticOpaque_3317_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 8, v_offsetCnstrs_3318_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 10, v_etaStruct_3319_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 11, v_univApprox_3320_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 12, v_iota_3321_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 13, v_beta_3322_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 14, v_proj_3323_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 15, v_zeta_3324_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 16, v_zetaDelta_3325_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 17, v_zetaUnused_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3376_, 18, v_zetaHave_3327_);
v_config_3343_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
uint64_t v___x_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3368_; 
lean_ctor_set_uint8(v_config_3343_, 9, v___x_3341_);
v___x_3344_ = l_Lean_Meta_Context_configKey(v___y_3288_);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___y_3288_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; lean_object* v_unused_3370_; lean_object* v_unused_3371_; lean_object* v_unused_3372_; lean_object* v_unused_3373_; lean_object* v_unused_3374_; lean_object* v_unused_3375_; 
v_unused_3369_ = lean_ctor_get(v___y_3288_, 6);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v___y_3288_, 5);
lean_dec(v_unused_3370_);
v_unused_3371_ = lean_ctor_get(v___y_3288_, 4);
lean_dec(v_unused_3371_);
v_unused_3372_ = lean_ctor_get(v___y_3288_, 3);
lean_dec(v_unused_3372_);
v_unused_3373_ = lean_ctor_get(v___y_3288_, 2);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v___y_3288_, 1);
lean_dec(v_unused_3374_);
v_unused_3375_ = lean_ctor_get(v___y_3288_, 0);
lean_dec(v_unused_3375_);
v___x_3346_ = v___y_3288_;
v_isShared_3347_ = v_isSharedCheck_3368_;
goto v_resetjp_3345_;
}
else
{
lean_dec(v___y_3288_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3368_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
uint64_t v___x_3348_; uint64_t v___x_3349_; uint64_t v___x_3350_; uint64_t v___x_3351_; uint64_t v_key_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3348_ = 2ULL;
v___x_3349_ = lean_uint64_shift_right(v___x_3344_, v___x_3348_);
v___x_3350_ = lean_uint64_shift_left(v___x_3349_, v___x_3348_);
v___x_3351_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonType___closed__0);
v_key_3352_ = lean_uint64_lor(v___x_3350_, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3353_, 0, v_config_3343_);
lean_ctor_set_uint64(v___x_3353_, sizeof(void*)*1, v_key_3352_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3353_);
v___x_3355_ = v___x_3346_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_zetaDeltaSet_3332_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_lctx_3333_);
lean_ctor_set(v_reuseFailAlloc_3367_, 3, v_localInstances_3334_);
lean_ctor_set(v_reuseFailAlloc_3367_, 4, v_defEqCtx_x3f_3335_);
lean_ctor_set(v_reuseFailAlloc_3367_, 5, v_synthPendingDepth_3336_);
lean_ctor_set(v_reuseFailAlloc_3367_, 6, v_canUnfold_x3f_3337_);
lean_ctor_set_uint8(v_reuseFailAlloc_3367_, sizeof(void*)*7, v_trackZetaDelta_3331_);
lean_ctor_set_uint8(v_reuseFailAlloc_3367_, sizeof(void*)*7 + 1, v_univApprox_3338_);
lean_ctor_set_uint8(v_reuseFailAlloc_3367_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3339_);
lean_ctor_set_uint8(v_reuseFailAlloc_3367_, sizeof(void*)*7 + 3, v_cacheInferType_3340_);
v___x_3355_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3356_; 
lean_inc(v_a_3271_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(v_e_3276_, v_f_3277_, v_a_3271_, v_a_3308_, v___y_3278_, v___y_3278_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___x_3355_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v___x_3356_);
v_arg_x27_3294_ = v_a_3357_;
goto v___jp_3293_;
}
else
{
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3358_; 
v_a_3358_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3356_);
v_arg_x27_3294_ = v_a_3358_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3359_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3356_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3356_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
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
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v_f_3277_);
lean_dec_ref(v_e_3276_);
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3378_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3307_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3307_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
case 1:
{
lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3386_ = lean_unsigned_to_nat(2u);
v___x_3387_ = l_Lean_Expr_isAppOfArity(v___x_3272_, v___x_3279_, v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; uint8_t v_foApprox_3389_; uint8_t v_ctxApprox_3390_; uint8_t v_quasiPatternApprox_3391_; uint8_t v_constApprox_3392_; uint8_t v_isDefEqStuckEx_3393_; uint8_t v_unificationHints_3394_; uint8_t v_proofIrrelevance_3395_; uint8_t v_assignSyntheticOpaque_3396_; uint8_t v_offsetCnstrs_3397_; uint8_t v_etaStruct_3398_; uint8_t v_univApprox_3399_; uint8_t v_iota_3400_; uint8_t v_beta_3401_; uint8_t v_proj_3402_; uint8_t v_zeta_3403_; uint8_t v_zetaDelta_3404_; uint8_t v_zetaUnused_3405_; uint8_t v_zetaHave_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v___y_3281_);
v___x_3388_ = l_Lean_Meta_Context_config(v___y_3288_);
v_foApprox_3389_ = lean_ctor_get_uint8(v___x_3388_, 0);
v_ctxApprox_3390_ = lean_ctor_get_uint8(v___x_3388_, 1);
v_quasiPatternApprox_3391_ = lean_ctor_get_uint8(v___x_3388_, 2);
v_constApprox_3392_ = lean_ctor_get_uint8(v___x_3388_, 3);
v_isDefEqStuckEx_3393_ = lean_ctor_get_uint8(v___x_3388_, 4);
v_unificationHints_3394_ = lean_ctor_get_uint8(v___x_3388_, 5);
v_proofIrrelevance_3395_ = lean_ctor_get_uint8(v___x_3388_, 6);
v_assignSyntheticOpaque_3396_ = lean_ctor_get_uint8(v___x_3388_, 7);
v_offsetCnstrs_3397_ = lean_ctor_get_uint8(v___x_3388_, 8);
v_etaStruct_3398_ = lean_ctor_get_uint8(v___x_3388_, 10);
v_univApprox_3399_ = lean_ctor_get_uint8(v___x_3388_, 11);
v_iota_3400_ = lean_ctor_get_uint8(v___x_3388_, 12);
v_beta_3401_ = lean_ctor_get_uint8(v___x_3388_, 13);
v_proj_3402_ = lean_ctor_get_uint8(v___x_3388_, 14);
v_zeta_3403_ = lean_ctor_get_uint8(v___x_3388_, 15);
v_zetaDelta_3404_ = lean_ctor_get_uint8(v___x_3388_, 16);
v_zetaUnused_3405_ = lean_ctor_get_uint8(v___x_3388_, 17);
v_zetaHave_3406_ = lean_ctor_get_uint8(v___x_3388_, 18);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3408_ = v___x_3388_;
v_isShared_3409_ = v_isSharedCheck_3456_;
goto v_resetjp_3407_;
}
else
{
lean_dec(v___x_3388_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3456_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
uint8_t v_trackZetaDelta_3410_; lean_object* v_zetaDeltaSet_3411_; lean_object* v_lctx_3412_; lean_object* v_localInstances_3413_; lean_object* v_defEqCtx_x3f_3414_; lean_object* v_synthPendingDepth_3415_; lean_object* v_canUnfold_x3f_3416_; uint8_t v_univApprox_3417_; uint8_t v_inTypeClassResolution_3418_; uint8_t v_cacheInferType_3419_; uint8_t v___x_3420_; lean_object* v_config_3422_; 
v_trackZetaDelta_3410_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7);
v_zetaDeltaSet_3411_ = lean_ctor_get(v___y_3288_, 1);
lean_inc(v_zetaDeltaSet_3411_);
v_lctx_3412_ = lean_ctor_get(v___y_3288_, 2);
lean_inc_ref(v_lctx_3412_);
v_localInstances_3413_ = lean_ctor_get(v___y_3288_, 3);
lean_inc_ref(v_localInstances_3413_);
v_defEqCtx_x3f_3414_ = lean_ctor_get(v___y_3288_, 4);
lean_inc(v_defEqCtx_x3f_3414_);
v_synthPendingDepth_3415_ = lean_ctor_get(v___y_3288_, 5);
lean_inc(v_synthPendingDepth_3415_);
v_canUnfold_x3f_3416_ = lean_ctor_get(v___y_3288_, 6);
lean_inc(v_canUnfold_x3f_3416_);
v_univApprox_3417_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3418_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 2);
v_cacheInferType_3419_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 3);
v___x_3420_ = 3;
if (v_isShared_3409_ == 0)
{
v_config_3422_ = v___x_3408_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 0, v_foApprox_3389_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 1, v_ctxApprox_3390_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 2, v_quasiPatternApprox_3391_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 3, v_constApprox_3392_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 4, v_isDefEqStuckEx_3393_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 5, v_unificationHints_3394_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 6, v_proofIrrelevance_3395_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 7, v_assignSyntheticOpaque_3396_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 8, v_offsetCnstrs_3397_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 10, v_etaStruct_3398_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 11, v_univApprox_3399_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 12, v_iota_3400_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 13, v_beta_3401_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 14, v_proj_3402_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 15, v_zeta_3403_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 16, v_zetaDelta_3404_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 17, v_zetaUnused_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3455_, 18, v_zetaHave_3406_);
v_config_3422_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
uint64_t v___x_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3447_; 
lean_ctor_set_uint8(v_config_3422_, 9, v___x_3420_);
v___x_3423_ = l_Lean_Meta_Context_configKey(v___y_3288_);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___y_3288_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; lean_object* v_unused_3449_; lean_object* v_unused_3450_; lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; lean_object* v_unused_3454_; 
v_unused_3448_ = lean_ctor_get(v___y_3288_, 6);
lean_dec(v_unused_3448_);
v_unused_3449_ = lean_ctor_get(v___y_3288_, 5);
lean_dec(v_unused_3449_);
v_unused_3450_ = lean_ctor_get(v___y_3288_, 4);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v___y_3288_, 3);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v___y_3288_, 2);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v___y_3288_, 1);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v___y_3288_, 0);
lean_dec(v_unused_3454_);
v___x_3425_ = v___y_3288_;
v_isShared_3426_ = v_isSharedCheck_3447_;
goto v_resetjp_3424_;
}
else
{
lean_dec(v___y_3288_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3447_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
uint64_t v___x_3427_; uint64_t v___x_3428_; uint64_t v___x_3429_; uint64_t v___x_3430_; uint64_t v_key_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3427_ = 2ULL;
v___x_3428_ = lean_uint64_shift_right(v___x_3423_, v___x_3427_);
v___x_3429_ = lean_uint64_shift_left(v___x_3428_, v___x_3427_);
v___x_3430_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonInst___closed__0);
v_key_3431_ = lean_uint64_lor(v___x_3429_, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3432_, 0, v_config_3422_);
lean_ctor_set_uint64(v___x_3432_, sizeof(void*)*1, v_key_3431_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3432_);
v___x_3434_ = v___x_3425_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_zetaDeltaSet_3411_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_lctx_3412_);
lean_ctor_set(v_reuseFailAlloc_3446_, 3, v_localInstances_3413_);
lean_ctor_set(v_reuseFailAlloc_3446_, 4, v_defEqCtx_x3f_3414_);
lean_ctor_set(v_reuseFailAlloc_3446_, 5, v_synthPendingDepth_3415_);
lean_ctor_set(v_reuseFailAlloc_3446_, 6, v_canUnfold_x3f_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3446_, sizeof(void*)*7, v_trackZetaDelta_3410_);
lean_ctor_set_uint8(v_reuseFailAlloc_3446_, sizeof(void*)*7 + 1, v_univApprox_3417_);
lean_ctor_set_uint8(v_reuseFailAlloc_3446_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3418_);
lean_ctor_set_uint8(v_reuseFailAlloc_3446_, sizeof(void*)*7 + 3, v_cacheInferType_3419_);
v___x_3434_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3435_; 
lean_inc_ref(v___x_3272_);
lean_inc(v_a_3271_);
v___x_3435_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(v_e_3276_, v_f_3277_, v_a_3271_, v___x_3272_, v___y_3274_, v___y_3274_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___x_3434_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref(v___x_3435_);
v_arg_x27_3294_ = v_a_3436_;
goto v___jp_3293_;
}
else
{
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3437_; 
v_a_3437_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3437_);
lean_dec_ref(v___x_3435_);
v_arg_x27_3294_ = v_a_3437_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3438_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3435_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3435_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
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
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_dec_ref(v_f_3277_);
lean_dec_ref(v_e_3276_);
v___x_3457_ = l_Lean_Expr_appFn_x21(v___x_3272_);
v___x_3458_ = l_Lean_Expr_appArg_x21(v___x_3457_);
lean_inc_ref(v___x_3458_);
v___x_3459_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v___x_3458_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; uint8_t v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_3458_, v_a_3460_);
lean_dec_ref(v___x_3458_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = l_Lean_Expr_appFn_x21(v___x_3457_);
lean_dec_ref(v___x_3457_);
v___x_3463_ = l_Lean_Expr_appArg_x21(v___x_3272_);
v___x_3464_ = l_Lean_mkAppB(v___x_3462_, v_a_3460_, v___x_3463_);
v_arg_x27_3294_ = v___x_3464_;
goto v___jp_3293_;
}
else
{
lean_dec(v_a_3460_);
lean_dec_ref(v___x_3457_);
lean_inc_ref(v___x_3272_);
v_arg_x27_3294_ = v___x_3272_;
goto v___jp_3293_;
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref(v___x_3458_);
lean_dec_ref(v___x_3457_);
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3465_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3459_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3459_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
case 2:
{
lean_object* v___x_3473_; 
lean_inc(v___y_3291_);
lean_inc_ref(v___y_3290_);
lean_inc(v___y_3289_);
lean_inc_ref(v___y_3288_);
lean_inc(v___y_3287_);
lean_inc_ref(v___y_3286_);
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc(v___y_3283_);
lean_inc(v___y_3282_);
lean_inc_ref(v___x_3272_);
v___x_3473_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v___x_3272_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; lean_object* v___x_3475_; uint8_t v_foApprox_3476_; uint8_t v_ctxApprox_3477_; uint8_t v_quasiPatternApprox_3478_; uint8_t v_constApprox_3479_; uint8_t v_isDefEqStuckEx_3480_; uint8_t v_unificationHints_3481_; uint8_t v_proofIrrelevance_3482_; uint8_t v_assignSyntheticOpaque_3483_; uint8_t v_offsetCnstrs_3484_; uint8_t v_etaStruct_3485_; uint8_t v_univApprox_3486_; uint8_t v_iota_3487_; uint8_t v_beta_3488_; uint8_t v_proj_3489_; uint8_t v_zeta_3490_; uint8_t v_zetaDelta_3491_; uint8_t v_zetaUnused_3492_; uint8_t v_zetaHave_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3543_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = l_Lean_Meta_Context_config(v___y_3288_);
v_foApprox_3476_ = lean_ctor_get_uint8(v___x_3475_, 0);
v_ctxApprox_3477_ = lean_ctor_get_uint8(v___x_3475_, 1);
v_quasiPatternApprox_3478_ = lean_ctor_get_uint8(v___x_3475_, 2);
v_constApprox_3479_ = lean_ctor_get_uint8(v___x_3475_, 3);
v_isDefEqStuckEx_3480_ = lean_ctor_get_uint8(v___x_3475_, 4);
v_unificationHints_3481_ = lean_ctor_get_uint8(v___x_3475_, 5);
v_proofIrrelevance_3482_ = lean_ctor_get_uint8(v___x_3475_, 6);
v_assignSyntheticOpaque_3483_ = lean_ctor_get_uint8(v___x_3475_, 7);
v_offsetCnstrs_3484_ = lean_ctor_get_uint8(v___x_3475_, 8);
v_etaStruct_3485_ = lean_ctor_get_uint8(v___x_3475_, 10);
v_univApprox_3486_ = lean_ctor_get_uint8(v___x_3475_, 11);
v_iota_3487_ = lean_ctor_get_uint8(v___x_3475_, 12);
v_beta_3488_ = lean_ctor_get_uint8(v___x_3475_, 13);
v_proj_3489_ = lean_ctor_get_uint8(v___x_3475_, 14);
v_zeta_3490_ = lean_ctor_get_uint8(v___x_3475_, 15);
v_zetaDelta_3491_ = lean_ctor_get_uint8(v___x_3475_, 16);
v_zetaUnused_3492_ = lean_ctor_get_uint8(v___x_3475_, 17);
v_zetaHave_3493_ = lean_ctor_get_uint8(v___x_3475_, 18);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3495_ = v___x_3475_;
v_isShared_3496_ = v_isSharedCheck_3543_;
goto v_resetjp_3494_;
}
else
{
lean_dec(v___x_3475_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3543_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
uint8_t v_trackZetaDelta_3497_; lean_object* v_zetaDeltaSet_3498_; lean_object* v_lctx_3499_; lean_object* v_localInstances_3500_; lean_object* v_defEqCtx_x3f_3501_; lean_object* v_synthPendingDepth_3502_; lean_object* v_canUnfold_x3f_3503_; uint8_t v_univApprox_3504_; uint8_t v_inTypeClassResolution_3505_; uint8_t v_cacheInferType_3506_; uint8_t v___x_3507_; lean_object* v_config_3509_; 
v_trackZetaDelta_3497_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7);
v_zetaDeltaSet_3498_ = lean_ctor_get(v___y_3288_, 1);
lean_inc(v_zetaDeltaSet_3498_);
v_lctx_3499_ = lean_ctor_get(v___y_3288_, 2);
lean_inc_ref(v_lctx_3499_);
v_localInstances_3500_ = lean_ctor_get(v___y_3288_, 3);
lean_inc_ref(v_localInstances_3500_);
v_defEqCtx_x3f_3501_ = lean_ctor_get(v___y_3288_, 4);
lean_inc(v_defEqCtx_x3f_3501_);
v_synthPendingDepth_3502_ = lean_ctor_get(v___y_3288_, 5);
lean_inc(v_synthPendingDepth_3502_);
v_canUnfold_x3f_3503_ = lean_ctor_get(v___y_3288_, 6);
lean_inc(v_canUnfold_x3f_3503_);
v_univApprox_3504_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3505_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 2);
v_cacheInferType_3506_ = lean_ctor_get_uint8(v___y_3288_, sizeof(void*)*7 + 3);
v___x_3507_ = 2;
if (v_isShared_3496_ == 0)
{
v_config_3509_ = v___x_3495_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 0, v_foApprox_3476_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 1, v_ctxApprox_3477_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 2, v_quasiPatternApprox_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 3, v_constApprox_3479_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 4, v_isDefEqStuckEx_3480_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 5, v_unificationHints_3481_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 6, v_proofIrrelevance_3482_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 7, v_assignSyntheticOpaque_3483_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 8, v_offsetCnstrs_3484_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 10, v_etaStruct_3485_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 11, v_univApprox_3486_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 12, v_iota_3487_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 13, v_beta_3488_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 14, v_proj_3489_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 15, v_zeta_3490_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 16, v_zetaDelta_3491_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 17, v_zetaUnused_3492_);
lean_ctor_set_uint8(v_reuseFailAlloc_3542_, 18, v_zetaHave_3493_);
v_config_3509_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
uint64_t v___x_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3534_; 
lean_ctor_set_uint8(v_config_3509_, 9, v___x_3507_);
v___x_3510_ = l_Lean_Meta_Context_configKey(v___y_3288_);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___y_3288_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; lean_object* v_unused_3536_; lean_object* v_unused_3537_; lean_object* v_unused_3538_; lean_object* v_unused_3539_; lean_object* v_unused_3540_; lean_object* v_unused_3541_; 
v_unused_3535_ = lean_ctor_get(v___y_3288_, 6);
lean_dec(v_unused_3535_);
v_unused_3536_ = lean_ctor_get(v___y_3288_, 5);
lean_dec(v_unused_3536_);
v_unused_3537_ = lean_ctor_get(v___y_3288_, 4);
lean_dec(v_unused_3537_);
v_unused_3538_ = lean_ctor_get(v___y_3288_, 3);
lean_dec(v_unused_3538_);
v_unused_3539_ = lean_ctor_get(v___y_3288_, 2);
lean_dec(v_unused_3539_);
v_unused_3540_ = lean_ctor_get(v___y_3288_, 1);
lean_dec(v_unused_3540_);
v_unused_3541_ = lean_ctor_get(v___y_3288_, 0);
lean_dec(v_unused_3541_);
v___x_3512_ = v___y_3288_;
v_isShared_3513_ = v_isSharedCheck_3534_;
goto v_resetjp_3511_;
}
else
{
lean_dec(v___y_3288_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3534_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
uint64_t v___x_3514_; uint64_t v___x_3515_; uint64_t v___x_3516_; uint64_t v___x_3517_; uint64_t v_key_3518_; lean_object* v___x_3519_; lean_object* v___x_3521_; 
v___x_3514_ = 2ULL;
v___x_3515_ = lean_uint64_shift_right(v___x_3510_, v___x_3514_);
v___x_3516_ = lean_uint64_shift_left(v___x_3515_, v___x_3514_);
v___x_3517_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImplicit___closed__0);
v_key_3518_ = lean_uint64_lor(v___x_3516_, v___x_3517_);
v___x_3519_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3519_, 0, v_config_3509_);
lean_ctor_set_uint64(v___x_3519_, sizeof(void*)*1, v_key_3518_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3519_);
v___x_3521_ = v___x_3512_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_zetaDeltaSet_3498_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_lctx_3499_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_localInstances_3500_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_defEqCtx_x3f_3501_);
lean_ctor_set(v_reuseFailAlloc_3533_, 5, v_synthPendingDepth_3502_);
lean_ctor_set(v_reuseFailAlloc_3533_, 6, v_canUnfold_x3f_3503_);
lean_ctor_set_uint8(v_reuseFailAlloc_3533_, sizeof(void*)*7, v_trackZetaDelta_3497_);
lean_ctor_set_uint8(v_reuseFailAlloc_3533_, sizeof(void*)*7 + 1, v_univApprox_3504_);
lean_ctor_set_uint8(v_reuseFailAlloc_3533_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3505_);
lean_ctor_set_uint8(v_reuseFailAlloc_3533_, sizeof(void*)*7 + 3, v_cacheInferType_3506_);
v___x_3521_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; 
lean_inc(v_a_3271_);
v___x_3522_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore(v_e_3276_, v_f_3277_, v_a_3271_, v_a_3474_, v___y_3274_, v___y_3278_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___x_3521_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref(v___x_3522_);
v_arg_x27_3294_ = v_a_3523_;
goto v___jp_3293_;
}
else
{
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3524_; 
v_a_3524_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3524_);
lean_dec_ref(v___x_3522_);
v_arg_x27_3294_ = v_a_3524_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3525_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3522_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3522_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
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
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v_f_3277_);
lean_dec_ref(v_e_3276_);
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3544_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3473_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3473_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
default: 
{
lean_object* v___x_3552_; 
lean_dec_ref(v_f_3277_);
lean_dec_ref(v_e_3276_);
lean_inc_ref(v___x_3272_);
v___x_3552_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v___x_3272_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v_arg_x27_3294_ = v_a_3553_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3554_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3552_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3552_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v_f_3277_);
lean_dec_ref(v_e_3276_);
lean_dec(v_fst_3275_);
lean_dec(v_snd_3273_);
lean_dec_ref(v___x_3272_);
lean_dec(v_a_3271_);
v_a_3562_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3304_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3304_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
v___jp_3293_:
{
uint8_t v___x_3295_; 
v___x_3295_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_3272_, v_arg_x27_3294_);
lean_dec_ref(v___x_3272_);
if (v___x_3295_ == 0)
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_fst_3275_);
v___x_3296_ = lean_array_fset(v_snd_3273_, v_a_3271_, v_arg_x27_3294_);
lean_dec(v_a_3271_);
v___x_3297_ = lean_box(v___y_3274_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v___x_3296_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
lean_dec_ref(v_arg_x27_3294_);
lean_dec(v_a_3271_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v_fst_3275_);
lean_ctor_set(v___x_3301_, 1, v_snd_3273_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
return v___x_3303_;
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__4));
v___x_3572_ = l_Lean_stringToMessageData(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__6));
v___x_3575_ = l_Lean_stringToMessageData(v___x_3574_);
return v___x_3575_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__8));
v___x_3578_ = l_Lean_stringToMessageData(v___x_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg(lean_object* v_upperBound_3579_, uint8_t v___y_3580_, lean_object* v___x_3581_, lean_object* v_e_3582_, lean_object* v_f_3583_, uint8_t v___y_3584_, lean_object* v_a_3585_, lean_object* v_b_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v___y_3600_; uint8_t v___x_3622_; 
v___x_3622_ = lean_nat_dec_lt(v_a_3585_, v_upperBound_3579_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; 
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v___x_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3623_, 0, v_b_3586_);
return v___x_3623_;
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3));
v___x_3625_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__2___redArg(v___x_3624_, v___y_3596_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v_fst_3627_; lean_object* v_snd_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3697_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref(v___x_3625_);
v_fst_3627_ = lean_ctor_get(v_b_3586_, 0);
v_snd_3628_ = lean_ctor_get(v_b_3586_, 1);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_b_3586_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3630_ = v_b_3586_;
v_isShared_3631_ = v_isSharedCheck_3697_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_snd_3628_);
lean_inc(v_fst_3627_);
lean_dec(v_b_3586_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3697_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3632_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3));
v___x_3633_ = lean_array_fget(v_snd_3628_, v_a_3585_);
v___x_3634_ = lean_unbox(v_a_3626_);
lean_dec(v_a_3626_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_del_object(v___x_3630_);
v___x_3635_ = lean_box(0);
lean_inc(v___y_3597_);
lean_inc_ref(v___y_3596_);
lean_inc(v___y_3595_);
lean_inc_ref(v___y_3594_);
lean_inc(v___y_3593_);
lean_inc_ref(v___y_3592_);
lean_inc(v___y_3591_);
lean_inc_ref(v___y_3590_);
lean_inc(v___y_3589_);
lean_inc(v___y_3588_);
lean_inc(v___y_3587_);
lean_inc_ref(v_f_3583_);
lean_inc_ref(v_e_3582_);
lean_inc(v_a_3585_);
v___x_3636_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___lam__0(v___x_3581_, v_a_3585_, v___x_3633_, v_snd_3628_, v___y_3580_, v_fst_3627_, v_e_3582_, v_f_3583_, v___y_3584_, v___x_3632_, v___x_3635_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
v___y_3600_ = v___x_3636_;
goto v___jp_3599_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Meta_Grind_updateLastTag(v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v___x_3638_; 
lean_dec_ref(v___x_3637_);
lean_inc(v___y_3597_);
lean_inc_ref(v___y_3596_);
lean_inc(v___y_3595_);
lean_inc_ref(v___y_3594_);
lean_inc(v___x_3633_);
v___x_3638_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_shouldCanon(v___x_3581_, v_a_3585_, v___x_3633_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3640_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v___x_3638_);
lean_inc(v___y_3597_);
lean_inc_ref(v___y_3596_);
lean_inc(v___y_3595_);
lean_inc_ref(v___y_3594_);
lean_inc(v___x_3633_);
v___x_3640_ = lean_infer_type(v___x_3633_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3642_; lean_object* v___y_3644_; uint8_t v___x_3668_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3640_);
v___x_3642_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__5);
v___x_3668_ = lean_unbox(v_a_3639_);
lean_dec(v_a_3639_);
switch(v___x_3668_)
{
case 0:
{
lean_object* v___x_3669_; 
v___x_3669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__1));
v___y_3644_ = v___x_3669_;
goto v___jp_3643_;
}
case 1:
{
lean_object* v___x_3670_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__3));
v___y_3644_ = v___x_3670_;
goto v___jp_3643_;
}
case 2:
{
lean_object* v___x_3671_; 
v___x_3671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__5));
v___y_3644_ = v___x_3671_;
goto v___jp_3643_;
}
default: 
{
lean_object* v___x_3672_; 
v___x_3672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instReprShouldCanonResult___lam__0___closed__7));
v___y_3644_ = v___x_3672_;
goto v___jp_3643_;
}
}
v___jp_3643_:
{
lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3645_ = l_Lean_MessageData_ofFormat(v___y_3644_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 7);
lean_ctor_set(v___x_3630_, 1, v___x_3645_);
lean_ctor_set(v___x_3630_, 0, v___x_3642_);
v___x_3647_ = v___x_3630_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3648_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__7);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
lean_inc(v___x_3633_);
v___x_3650_ = l_Lean_MessageData_ofExpr(v___x_3633_);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__9);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = l_Lean_MessageData_ofExpr(v_a_3641_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(v___x_3624_, v___x_3655_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
lean_inc(v___y_3597_);
lean_inc_ref(v___y_3596_);
lean_inc(v___y_3595_);
lean_inc_ref(v___y_3594_);
lean_inc(v___y_3593_);
lean_inc_ref(v___y_3592_);
lean_inc(v___y_3591_);
lean_inc_ref(v___y_3590_);
lean_inc(v___y_3589_);
lean_inc(v___y_3588_);
lean_inc(v___y_3587_);
lean_inc_ref(v_f_3583_);
lean_inc_ref(v_e_3582_);
lean_inc(v_a_3585_);
v___x_3658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___lam__0(v___x_3581_, v_a_3585_, v___x_3633_, v_snd_3628_, v___y_3580_, v_fst_3627_, v_e_3582_, v_f_3583_, v___y_3584_, v___x_3632_, v_a_3657_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
v___y_3600_ = v___x_3658_;
goto v___jp_3599_;
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v___x_3633_);
lean_dec(v_snd_3628_);
lean_dec(v_fst_3627_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v_a_3659_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3656_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3656_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
lean_dec(v_a_3639_);
lean_dec(v___x_3633_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_fst_3627_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v_a_3673_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3640_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3640_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec(v___x_3633_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_fst_3627_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v_a_3681_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3638_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3638_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v___x_3633_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_fst_3627_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v_a_3689_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3637_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3637_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v_b_3586_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v_a_3698_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3625_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3625_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
v___jp_3599_:
{
if (lean_obj_tag(v___y_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3613_; 
v_a_3601_ = lean_ctor_get(v___y_3600_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___y_3600_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3603_ = v___y_3600_;
v_isShared_3604_ = v_isSharedCheck_3613_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___y_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3613_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
if (lean_obj_tag(v_a_3601_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; 
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v_a_3605_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v_a_3601_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v_a_3605_);
v___x_3607_ = v___x_3603_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3603_);
v_a_3609_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v_a_3601_);
v___x_3610_ = lean_unsigned_to_nat(1u);
v___x_3611_ = lean_nat_add(v_a_3585_, v___x_3610_);
lean_dec(v_a_3585_);
v_a_3585_ = v___x_3611_;
v_b_3586_ = v_a_3609_;
goto _start;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec(v_a_3585_);
lean_dec_ref(v_f_3583_);
lean_dec_ref(v_e_3582_);
v_a_3614_ = lean_ctor_get(v___y_3600_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___y_3600_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___y_3600_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___y_3600_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(lean_object* v_e_3711_, uint8_t v___y_3712_, lean_object* v_x_3713_, lean_object* v_x_3714_, lean_object* v_x_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v___y_3729_; lean_object* v_args_3730_; uint8_t v_modified_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; uint8_t v___y_3791_; lean_object* v___y_3824_; lean_object* v___y_3825_; 
if (lean_obj_tag(v_x_3713_) == 5)
{
lean_object* v_fn_3878_; lean_object* v_arg_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_fn_3878_ = lean_ctor_get(v_x_3713_, 0);
lean_inc_ref(v_fn_3878_);
v_arg_3879_ = lean_ctor_get(v_x_3713_, 1);
lean_inc_ref(v_arg_3879_);
lean_dec_ref(v_x_3713_);
v___x_3880_ = lean_array_set(v_x_3714_, v_x_3715_, v_arg_3879_);
v___x_3881_ = lean_unsigned_to_nat(1u);
v___x_3882_ = lean_nat_sub(v_x_3715_, v___x_3881_);
lean_dec(v_x_3715_);
v_x_3713_ = v_fn_3878_;
v_x_3714_ = v___x_3880_;
v_x_3715_ = v___x_3882_;
goto _start;
}
else
{
uint8_t v___y_3885_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
lean_dec(v_x_3715_);
v___x_3911_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___closed__1));
v___x_3912_ = l_Lean_Expr_isConstOf(v_x_3713_, v___x_3911_);
if (v___x_3912_ == 0)
{
v___y_3885_ = v___x_3912_;
goto v___jp_3884_;
}
else
{
lean_object* v___x_3913_; uint8_t v___x_3914_; 
v___x_3913_ = lean_box(0);
v___x_3914_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___lam__0(v_x_3714_, v___x_3913_);
v___y_3885_ = v___x_3914_;
goto v___jp_3884_;
}
v___jp_3884_:
{
if (v___y_3885_ == 0)
{
lean_object* v___x_3886_; uint8_t v___x_3887_; 
v___x_3886_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___closed__3));
v___x_3887_ = l_Lean_Expr_isConstOf(v_x_3713_, v___x_3886_);
if (v___x_3887_ == 0)
{
v___y_3791_ = v___x_3887_;
goto v___jp_3790_;
}
else
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = lean_box(0);
v___x_3889_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___lam__0(v_x_3714_, v___x_3888_);
v___y_3791_ = v___x_3889_;
goto v___jp_3790_;
}
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3890_ = l_Lean_instInhabitedExpr;
v___x_3891_ = lean_unsigned_to_nat(0u);
v___x_3892_ = lean_array_get_borrowed(v___x_3890_, v_x_3714_, v___x_3891_);
lean_inc(v___y_3717_);
lean_inc(v___x_3892_);
v___x_3893_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v___x_3892_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3910_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3910_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3910_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3898_; lean_object* v_toGoalState_3899_; lean_object* v_canon_3900_; lean_object* v_proofCanon_3901_; lean_object* v___x_3902_; 
v___x_3898_ = lean_st_ref_get(v___y_3717_);
v_toGoalState_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc_ref(v_toGoalState_3899_);
lean_dec(v___x_3898_);
v_canon_3900_ = lean_ctor_get(v_toGoalState_3899_, 1);
lean_inc_ref(v_canon_3900_);
lean_dec_ref(v_toGoalState_3899_);
v_proofCanon_3901_ = lean_ctor_get(v_canon_3900_, 2);
lean_inc_ref(v_proofCanon_3901_);
lean_dec_ref(v_canon_3900_);
v___x_3902_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(v_proofCanon_3901_, v_a_3894_);
if (lean_obj_tag(v___x_3902_) == 1)
{
lean_object* v_val_3903_; lean_object* v___x_3905_; 
lean_dec(v_a_3894_);
lean_dec(v___y_3717_);
lean_dec_ref(v_x_3714_);
lean_dec_ref(v_x_3713_);
lean_dec_ref(v_e_3711_);
v_val_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_val_3903_);
lean_dec_ref(v___x_3902_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v_val_3903_);
v___x_3905_ = v___x_3896_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_val_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
else
{
uint8_t v___x_3907_; 
lean_dec(v___x_3902_);
lean_del_object(v___x_3896_);
v___x_3907_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_3892_, v_a_3894_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v_e_3711_);
lean_inc(v_a_3894_);
v___x_3908_ = lean_array_set(v_x_3714_, v___x_3891_, v_a_3894_);
v___x_3909_ = l_Lean_mkAppN(v_x_3713_, v___x_3908_);
lean_dec_ref(v___x_3908_);
v___y_3824_ = v_a_3894_;
v___y_3825_ = v___x_3909_;
goto v___jp_3823_;
}
else
{
lean_dec_ref(v_x_3714_);
lean_dec_ref(v_x_3713_);
v___y_3824_ = v_a_3894_;
v___y_3825_ = v_e_3711_;
goto v___jp_3823_;
}
}
}
}
else
{
lean_dec(v___y_3717_);
lean_dec_ref(v_x_3714_);
lean_dec_ref(v_x_3713_);
lean_dec_ref(v_e_3711_);
return v___x_3893_;
}
}
}
}
v___jp_3728_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = lean_box(0);
lean_inc(v___y_3742_);
lean_inc_ref(v___y_3741_);
lean_inc(v___y_3740_);
lean_inc_ref(v___y_3739_);
lean_inc_ref(v_x_3713_);
v___x_3744_ = l_Lean_Meta_getFunInfo(v_x_3713_, v___x_3743_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v_paramInfo_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3780_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref(v___x_3744_);
v_paramInfo_3746_ = lean_ctor_get(v_a_3745_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v_a_3745_);
if (v_isSharedCheck_3780_ == 0)
{
lean_object* v_unused_3781_; 
v_unused_3781_ = lean_ctor_get(v_a_3745_, 1);
lean_dec(v_unused_3781_);
v___x_3748_ = v_a_3745_;
v_isShared_3749_ = v_isSharedCheck_3780_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_paramInfo_3746_);
lean_dec(v_a_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3780_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3750_ = lean_array_get_size(v_args_3730_);
v___x_3751_ = lean_unsigned_to_nat(0u);
v___x_3752_ = lean_box(v_modified_3731_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 1, v_args_3730_);
lean_ctor_set(v___x_3748_, 0, v___x_3752_);
v___x_3754_ = v___x_3748_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_args_3730_);
v___x_3754_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; 
lean_inc_ref(v_x_3713_);
lean_inc_ref(v_e_3711_);
v___x_3755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg(v___x_3750_, v___y_3712_, v_paramInfo_3746_, v_e_3711_, v_x_3713_, v___y_3729_, v___x_3751_, v___x_3754_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec_ref(v_paramInfo_3746_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3770_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3770_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3770_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v_fst_3760_; uint8_t v___x_3761_; 
v_fst_3760_ = lean_ctor_get(v_a_3756_, 0);
v___x_3761_ = lean_unbox(v_fst_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3763_; 
lean_dec(v_a_3756_);
lean_dec_ref(v_x_3713_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v_e_3711_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_e_3711_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
else
{
lean_object* v_snd_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec_ref(v_e_3711_);
v_snd_3765_ = lean_ctor_get(v_a_3756_, 1);
lean_inc(v_snd_3765_);
lean_dec(v_a_3756_);
v___x_3766_ = l_Lean_mkAppN(v_x_3713_, v_snd_3765_);
lean_dec(v_snd_3765_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3766_);
v___x_3768_ = v___x_3758_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec_ref(v_x_3713_);
lean_dec_ref(v_e_3711_);
v_a_3771_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3755_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3755_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v_args_3730_);
lean_dec_ref(v_x_3713_);
lean_dec_ref(v_e_3711_);
v_a_3782_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3744_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3744_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
v___jp_3790_:
{
if (v___y_3791_ == 0)
{
lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f___closed__6));
v___x_3793_ = l_Lean_Expr_isConstOf(v_x_3713_, v___x_3792_);
if (v___x_3793_ == 0)
{
v___y_3729_ = v___y_3791_;
v_args_3730_ = v_x_3714_;
v_modified_3731_ = v___y_3791_;
v___y_3732_ = v___y_3716_;
v___y_3733_ = v___y_3717_;
v___y_3734_ = v___y_3718_;
v___y_3735_ = v___y_3719_;
v___y_3736_ = v___y_3720_;
v___y_3737_ = v___y_3721_;
v___y_3738_ = v___y_3722_;
v___y_3739_ = v___y_3723_;
v___y_3740_ = v___y_3724_;
v___y_3741_ = v___y_3725_;
v___y_3742_ = v___y_3726_;
goto v___jp_3728_;
}
else
{
lean_object* v___x_3794_; 
lean_inc(v___y_3726_);
lean_inc_ref(v___y_3725_);
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3723_);
lean_inc_ref(v_x_3714_);
v___x_3794_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_normOfNatArgs_x3f(v_x_3714_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
if (lean_obj_tag(v_a_3795_) == 1)
{
lean_object* v_val_3796_; 
lean_dec_ref(v_x_3714_);
v_val_3796_ = lean_ctor_get(v_a_3795_, 0);
lean_inc(v_val_3796_);
lean_dec_ref(v_a_3795_);
v___y_3729_ = v___y_3791_;
v_args_3730_ = v_val_3796_;
v_modified_3731_ = v___y_3712_;
v___y_3732_ = v___y_3716_;
v___y_3733_ = v___y_3717_;
v___y_3734_ = v___y_3718_;
v___y_3735_ = v___y_3719_;
v___y_3736_ = v___y_3720_;
v___y_3737_ = v___y_3721_;
v___y_3738_ = v___y_3722_;
v___y_3739_ = v___y_3723_;
v___y_3740_ = v___y_3724_;
v___y_3741_ = v___y_3725_;
v___y_3742_ = v___y_3726_;
goto v___jp_3728_;
}
else
{
lean_dec(v_a_3795_);
v___y_3729_ = v___y_3791_;
v_args_3730_ = v_x_3714_;
v_modified_3731_ = v___y_3791_;
v___y_3732_ = v___y_3716_;
v___y_3733_ = v___y_3717_;
v___y_3734_ = v___y_3718_;
v___y_3735_ = v___y_3719_;
v___y_3736_ = v___y_3720_;
v___y_3737_ = v___y_3721_;
v___y_3738_ = v___y_3722_;
v___y_3739_ = v___y_3723_;
v___y_3740_ = v___y_3724_;
v___y_3741_ = v___y_3725_;
v___y_3742_ = v___y_3726_;
goto v___jp_3728_;
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v_x_3714_);
lean_dec_ref(v_x_3713_);
lean_dec_ref(v_e_3711_);
v_a_3797_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3794_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3794_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3805_ = l_Lean_instInhabitedExpr;
v___x_3806_ = lean_unsigned_to_nat(0u);
v___x_3807_ = lean_array_get_borrowed(v___x_3805_, v_x_3714_, v___x_3806_);
lean_inc(v___x_3807_);
v___x_3808_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v___x_3807_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3822_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3822_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3822_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
uint8_t v___x_3813_; 
v___x_3813_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_3807_, v_a_3809_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
lean_dec_ref(v_e_3711_);
v___x_3814_ = lean_array_set(v_x_3714_, v___x_3806_, v_a_3809_);
v___x_3815_ = l_Lean_mkAppN(v_x_3713_, v___x_3814_);
lean_dec_ref(v___x_3814_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v___x_3815_);
v___x_3817_ = v___x_3811_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
else
{
lean_object* v___x_3820_; 
lean_dec(v_a_3809_);
lean_dec_ref(v_x_3714_);
lean_dec_ref(v_x_3713_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 0, v_e_3711_);
v___x_3820_ = v___x_3811_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_e_3711_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
lean_dec_ref(v_x_3714_);
lean_dec_ref(v_x_3713_);
lean_dec_ref(v_e_3711_);
return v___x_3808_;
}
}
}
v___jp_3823_:
{
lean_object* v___x_3826_; lean_object* v_toGoalState_3827_; lean_object* v_canon_3828_; lean_object* v_mvarId_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3876_; 
v___x_3826_ = lean_st_ref_take(v___y_3717_);
v_toGoalState_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc_ref(v_toGoalState_3827_);
v_canon_3828_ = lean_ctor_get(v_toGoalState_3827_, 1);
lean_inc_ref(v_canon_3828_);
v_mvarId_3829_ = lean_ctor_get(v___x_3826_, 1);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; 
v_unused_3877_ = lean_ctor_get(v___x_3826_, 0);
lean_dec(v_unused_3877_);
v___x_3831_ = v___x_3826_;
v_isShared_3832_ = v_isSharedCheck_3876_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_mvarId_3829_);
lean_dec(v___x_3826_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3876_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v_nextDeclIdx_3833_; lean_object* v_enodeMap_3834_; lean_object* v_exprs_3835_; lean_object* v_parents_3836_; lean_object* v_congrTable_3837_; lean_object* v_appMap_3838_; lean_object* v_indicesFound_3839_; lean_object* v_newFacts_3840_; uint8_t v_inconsistent_3841_; lean_object* v_nextIdx_3842_; lean_object* v_newRawFacts_3843_; lean_object* v_facts_3844_; lean_object* v_extThms_3845_; lean_object* v_ematch_3846_; lean_object* v_inj_3847_; lean_object* v_split_3848_; lean_object* v_clean_3849_; lean_object* v_sstates_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3874_; 
v_nextDeclIdx_3833_ = lean_ctor_get(v_toGoalState_3827_, 0);
v_enodeMap_3834_ = lean_ctor_get(v_toGoalState_3827_, 2);
v_exprs_3835_ = lean_ctor_get(v_toGoalState_3827_, 3);
v_parents_3836_ = lean_ctor_get(v_toGoalState_3827_, 4);
v_congrTable_3837_ = lean_ctor_get(v_toGoalState_3827_, 5);
v_appMap_3838_ = lean_ctor_get(v_toGoalState_3827_, 6);
v_indicesFound_3839_ = lean_ctor_get(v_toGoalState_3827_, 7);
v_newFacts_3840_ = lean_ctor_get(v_toGoalState_3827_, 8);
v_inconsistent_3841_ = lean_ctor_get_uint8(v_toGoalState_3827_, sizeof(void*)*18);
v_nextIdx_3842_ = lean_ctor_get(v_toGoalState_3827_, 9);
v_newRawFacts_3843_ = lean_ctor_get(v_toGoalState_3827_, 10);
v_facts_3844_ = lean_ctor_get(v_toGoalState_3827_, 11);
v_extThms_3845_ = lean_ctor_get(v_toGoalState_3827_, 12);
v_ematch_3846_ = lean_ctor_get(v_toGoalState_3827_, 13);
v_inj_3847_ = lean_ctor_get(v_toGoalState_3827_, 14);
v_split_3848_ = lean_ctor_get(v_toGoalState_3827_, 15);
v_clean_3849_ = lean_ctor_get(v_toGoalState_3827_, 16);
v_sstates_3850_ = lean_ctor_get(v_toGoalState_3827_, 17);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_toGoalState_3827_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; 
v_unused_3875_ = lean_ctor_get(v_toGoalState_3827_, 1);
lean_dec(v_unused_3875_);
v___x_3852_ = v_toGoalState_3827_;
v_isShared_3853_ = v_isSharedCheck_3874_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_sstates_3850_);
lean_inc(v_clean_3849_);
lean_inc(v_split_3848_);
lean_inc(v_inj_3847_);
lean_inc(v_ematch_3846_);
lean_inc(v_extThms_3845_);
lean_inc(v_facts_3844_);
lean_inc(v_newRawFacts_3843_);
lean_inc(v_nextIdx_3842_);
lean_inc(v_newFacts_3840_);
lean_inc(v_indicesFound_3839_);
lean_inc(v_appMap_3838_);
lean_inc(v_congrTable_3837_);
lean_inc(v_parents_3836_);
lean_inc(v_exprs_3835_);
lean_inc(v_enodeMap_3834_);
lean_inc(v_nextDeclIdx_3833_);
lean_dec(v_toGoalState_3827_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3874_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v_argMap_3854_; lean_object* v_canon_3855_; lean_object* v_proofCanon_3856_; lean_object* v_canonArg_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3873_; 
v_argMap_3854_ = lean_ctor_get(v_canon_3828_, 0);
v_canon_3855_ = lean_ctor_get(v_canon_3828_, 1);
v_proofCanon_3856_ = lean_ctor_get(v_canon_3828_, 2);
v_canonArg_3857_ = lean_ctor_get(v_canon_3828_, 3);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_canon_3828_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3859_ = v_canon_3828_;
v_isShared_3860_ = v_isSharedCheck_3873_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_canonArg_3857_);
lean_inc(v_proofCanon_3856_);
lean_inc(v_canon_3855_);
lean_inc(v_argMap_3854_);
lean_dec(v_canon_3828_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3873_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
lean_inc_ref(v___y_3825_);
v___x_3861_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__0___redArg(v_proofCanon_3856_, v___y_3824_, v___y_3825_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 2, v___x_3861_);
v___x_3863_ = v___x_3859_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_argMap_3854_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_canon_3855_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_canonArg_3857_);
v___x_3863_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3865_; 
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 1, v___x_3863_);
v___x_3865_ = v___x_3852_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_nextDeclIdx_3833_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_enodeMap_3834_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v_exprs_3835_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v_parents_3836_);
lean_ctor_set(v_reuseFailAlloc_3871_, 5, v_congrTable_3837_);
lean_ctor_set(v_reuseFailAlloc_3871_, 6, v_appMap_3838_);
lean_ctor_set(v_reuseFailAlloc_3871_, 7, v_indicesFound_3839_);
lean_ctor_set(v_reuseFailAlloc_3871_, 8, v_newFacts_3840_);
lean_ctor_set(v_reuseFailAlloc_3871_, 9, v_nextIdx_3842_);
lean_ctor_set(v_reuseFailAlloc_3871_, 10, v_newRawFacts_3843_);
lean_ctor_set(v_reuseFailAlloc_3871_, 11, v_facts_3844_);
lean_ctor_set(v_reuseFailAlloc_3871_, 12, v_extThms_3845_);
lean_ctor_set(v_reuseFailAlloc_3871_, 13, v_ematch_3846_);
lean_ctor_set(v_reuseFailAlloc_3871_, 14, v_inj_3847_);
lean_ctor_set(v_reuseFailAlloc_3871_, 15, v_split_3848_);
lean_ctor_set(v_reuseFailAlloc_3871_, 16, v_clean_3849_);
lean_ctor_set(v_reuseFailAlloc_3871_, 17, v_sstates_3850_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*18, v_inconsistent_3841_);
v___x_3865_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3867_; 
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v___x_3865_);
v___x_3867_ = v___x_3831_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_mvarId_3829_);
v___x_3867_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_st_ref_set(v___y_3717_, v___x_3867_);
lean_dec(v___y_3717_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___y_3825_);
return v___x_3869_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(lean_object* v_e_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_e_x27_3929_; lean_object* v___y_3930_; uint8_t v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; uint8_t v___y_3941_; lean_object* v___y_3946_; lean_object* v___y_3947_; uint8_t v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v_b_x27_3951_; lean_object* v___y_3952_; uint8_t v___y_3960_; uint8_t v___x_3991_; 
v___x_3991_ = l_Lean_Expr_isApp(v_e_3915_);
if (v___x_3991_ == 0)
{
uint8_t v___x_3992_; 
v___x_3992_ = l_Lean_Expr_isForall(v_e_3915_);
v___y_3960_ = v___x_3992_;
goto v___jp_3959_;
}
else
{
v___y_3960_ = v___x_3991_;
goto v___jp_3959_;
}
v___jp_3928_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3931_ = lean_st_ref_take(v___y_3930_);
lean_inc_ref(v_e_x27_3929_);
v___x_3932_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(v___x_3931_, v_e_3915_, v_e_x27_3929_);
v___x_3933_ = lean_st_ref_set(v___y_3930_, v___x_3932_);
lean_dec(v___y_3930_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_e_x27_3929_);
return v___x_3934_;
}
v___jp_3935_:
{
if (v___y_3941_ == 0)
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_Expr_forallE___override(v___y_3937_, v___y_3940_, v___y_3938_, v___y_3936_);
v_e_x27_3929_ = v___x_3942_;
v___y_3930_ = v___y_3939_;
goto v___jp_3928_;
}
else
{
uint8_t v___x_3943_; 
v___x_3943_ = l_Lean_instBEqBinderInfo_beq(v___y_3936_, v___y_3936_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_Expr_forallE___override(v___y_3937_, v___y_3940_, v___y_3938_, v___y_3936_);
v_e_x27_3929_ = v___x_3944_;
v___y_3930_ = v___y_3939_;
goto v___jp_3928_;
}
else
{
lean_dec_ref(v___y_3940_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_inc_ref(v_e_3915_);
v_e_x27_3929_ = v_e_3915_;
v___y_3930_ = v___y_3939_;
goto v___jp_3928_;
}
}
}
v___jp_3945_:
{
size_t v___x_3953_; size_t v___x_3954_; uint8_t v___x_3955_; 
v___x_3953_ = lean_ptr_addr(v___y_3946_);
lean_dec_ref(v___y_3946_);
v___x_3954_ = lean_ptr_addr(v___y_3950_);
v___x_3955_ = lean_usize_dec_eq(v___x_3953_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_dec_ref(v___y_3949_);
v___y_3936_ = v___y_3948_;
v___y_3937_ = v___y_3947_;
v___y_3938_ = v_b_x27_3951_;
v___y_3939_ = v___y_3952_;
v___y_3940_ = v___y_3950_;
v___y_3941_ = v___x_3955_;
goto v___jp_3935_;
}
else
{
size_t v___x_3956_; size_t v___x_3957_; uint8_t v___x_3958_; 
v___x_3956_ = lean_ptr_addr(v___y_3949_);
lean_dec_ref(v___y_3949_);
v___x_3957_ = lean_ptr_addr(v_b_x27_3951_);
v___x_3958_ = lean_usize_dec_eq(v___x_3956_, v___x_3957_);
v___y_3936_ = v___y_3948_;
v___y_3937_ = v___y_3947_;
v___y_3938_ = v_b_x27_3951_;
v___y_3939_ = v___y_3952_;
v___y_3940_ = v___y_3950_;
v___y_3941_ = v___x_3958_;
goto v___jp_3935_;
}
}
v___jp_3959_:
{
if (v___y_3960_ == 0)
{
lean_object* v___x_3961_; 
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec(v_a_3916_);
v___x_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3961_, 0, v_e_3915_);
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_st_ref_get(v_a_3916_);
v___x_3963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(v___x_3962_, v_e_3915_);
lean_dec(v___x_3962_);
if (lean_obj_tag(v___x_3963_) == 1)
{
lean_object* v_val_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec(v_a_3916_);
lean_dec_ref(v_e_3915_);
v_val_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_val_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
lean_ctor_set_tag(v___x_3966_, 0);
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_val_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_dec(v___x_3963_);
switch(lean_obj_tag(v_e_3915_))
{
case 5:
{
lean_object* v_dummy_3972_; lean_object* v_nargs_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_dummy_3972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__0, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__0);
v_nargs_3973_ = l_Lean_Expr_getAppNumArgs(v_e_3915_);
lean_inc(v_nargs_3973_);
v___x_3974_ = lean_mk_array(v_nargs_3973_, v_dummy_3972_);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = lean_nat_sub(v_nargs_3973_, v___x_3975_);
lean_dec(v_nargs_3973_);
lean_inc(v_a_3916_);
lean_inc_ref_n(v_e_3915_, 2);
v___x_3977_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(v_e_3915_, v___y_3960_, v_e_3915_, v___x_3974_, v___x_3976_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref(v___x_3977_);
v_e_x27_3929_ = v_a_3978_;
v___y_3930_ = v_a_3916_;
goto v___jp_3928_;
}
else
{
lean_dec_ref(v_e_3915_);
lean_dec(v_a_3916_);
return v___x_3977_;
}
}
case 7:
{
lean_object* v_binderName_3979_; lean_object* v_binderType_3980_; lean_object* v_body_3981_; uint8_t v_binderInfo_3982_; lean_object* v___x_3983_; 
v_binderName_3979_ = lean_ctor_get(v_e_3915_, 0);
v_binderType_3980_ = lean_ctor_get(v_e_3915_, 1);
v_body_3981_ = lean_ctor_get(v_e_3915_, 2);
v_binderInfo_3982_ = lean_ctor_get_uint8(v_e_3915_, sizeof(void*)*3 + 8);
lean_inc(v_a_3926_);
lean_inc_ref(v_a_3925_);
lean_inc(v_a_3924_);
lean_inc_ref(v_a_3923_);
lean_inc(v_a_3922_);
lean_inc_ref(v_a_3921_);
lean_inc(v_a_3920_);
lean_inc_ref(v_a_3919_);
lean_inc(v_a_3918_);
lean_inc(v_a_3917_);
lean_inc(v_a_3916_);
lean_inc_ref(v_binderType_3980_);
v___x_3983_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v_binderType_3980_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; uint8_t v___x_3985_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref(v___x_3983_);
v___x_3985_ = l_Lean_Expr_hasLooseBVars(v_body_3981_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
lean_inc(v_a_3916_);
lean_inc_ref(v_body_3981_);
v___x_3986_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v_body_3981_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref(v___x_3986_);
lean_inc_ref(v_body_3981_);
lean_inc(v_binderName_3979_);
lean_inc_ref(v_binderType_3980_);
v___y_3946_ = v_binderType_3980_;
v___y_3947_ = v_binderName_3979_;
v___y_3948_ = v_binderInfo_3982_;
v___y_3949_ = v_body_3981_;
v___y_3950_ = v_a_3984_;
v_b_x27_3951_ = v_a_3987_;
v___y_3952_ = v_a_3916_;
goto v___jp_3945_;
}
else
{
lean_dec(v_a_3984_);
lean_dec_ref(v_e_3915_);
lean_dec(v_a_3916_);
return v___x_3986_;
}
}
else
{
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec(v_a_3917_);
lean_inc_ref_n(v_body_3981_, 2);
lean_inc(v_binderName_3979_);
lean_inc_ref(v_binderType_3980_);
v___y_3946_ = v_binderType_3980_;
v___y_3947_ = v_binderName_3979_;
v___y_3948_ = v_binderInfo_3982_;
v___y_3949_ = v_body_3981_;
v___y_3950_ = v_a_3984_;
v_b_x27_3951_ = v_body_3981_;
v___y_3952_ = v_a_3916_;
goto v___jp_3945_;
}
}
else
{
lean_dec_ref(v_e_3915_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec(v_a_3916_);
return v___x_3983_;
}
}
default: 
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__4, &l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___closed__4);
lean_inc(v_a_3916_);
v___x_3989_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__7(v___x_3988_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref(v___x_3989_);
v_e_x27_3929_ = v_a_3990_;
v___y_3930_ = v_a_3916_;
goto v___jp_3928_;
}
else
{
lean_dec(v_a_3916_);
lean_dec_ref(v_e_3915_);
return v___x_3989_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit___boxed(lean_object* v_e_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_){
_start:
{
lean_object* v_res_4006_; 
v_res_4006_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v_e_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
return v_res_4006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4007_ = _args[0];
lean_object* v___y_4008_ = _args[1];
lean_object* v___x_4009_ = _args[2];
lean_object* v_e_4010_ = _args[3];
lean_object* v_f_4011_ = _args[4];
lean_object* v___y_4012_ = _args[5];
lean_object* v_a_4013_ = _args[6];
lean_object* v_b_4014_ = _args[7];
lean_object* v___y_4015_ = _args[8];
lean_object* v___y_4016_ = _args[9];
lean_object* v___y_4017_ = _args[10];
lean_object* v___y_4018_ = _args[11];
lean_object* v___y_4019_ = _args[12];
lean_object* v___y_4020_ = _args[13];
lean_object* v___y_4021_ = _args[14];
lean_object* v___y_4022_ = _args[15];
lean_object* v___y_4023_ = _args[16];
lean_object* v___y_4024_ = _args[17];
lean_object* v___y_4025_ = _args[18];
lean_object* v___y_4026_ = _args[19];
_start:
{
uint8_t v___y_146144__boxed_4027_; uint8_t v___y_146146__boxed_4028_; lean_object* v_res_4029_; 
v___y_146144__boxed_4027_ = lean_unbox(v___y_4008_);
v___y_146146__boxed_4028_ = lean_unbox(v___y_4012_);
v_res_4029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg(v_upperBound_4007_, v___y_146144__boxed_4027_, v___x_4009_, v_e_4010_, v_f_4011_, v___y_146146__boxed_4028_, v_a_4013_, v_b_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec_ref(v___x_4009_);
lean_dec(v_upperBound_4007_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_4030_ = _args[0];
lean_object* v_a_4031_ = _args[1];
lean_object* v___x_4032_ = _args[2];
lean_object* v_snd_4033_ = _args[3];
lean_object* v___y_4034_ = _args[4];
lean_object* v_fst_4035_ = _args[5];
lean_object* v_e_4036_ = _args[6];
lean_object* v_f_4037_ = _args[7];
lean_object* v___y_4038_ = _args[8];
lean_object* v___x_4039_ = _args[9];
lean_object* v_____r_4040_ = _args[10];
lean_object* v___y_4041_ = _args[11];
lean_object* v___y_4042_ = _args[12];
lean_object* v___y_4043_ = _args[13];
lean_object* v___y_4044_ = _args[14];
lean_object* v___y_4045_ = _args[15];
lean_object* v___y_4046_ = _args[16];
lean_object* v___y_4047_ = _args[17];
lean_object* v___y_4048_ = _args[18];
lean_object* v___y_4049_ = _args[19];
lean_object* v___y_4050_ = _args[20];
lean_object* v___y_4051_ = _args[21];
lean_object* v___y_4052_ = _args[22];
_start:
{
uint8_t v___y_146217__boxed_4053_; uint8_t v___y_146218__boxed_4054_; lean_object* v_res_4055_; 
v___y_146217__boxed_4053_ = lean_unbox(v___y_4034_);
v___y_146218__boxed_4054_ = lean_unbox(v___y_4038_);
v_res_4055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg___lam__0(v___x_4030_, v_a_4031_, v___x_4032_, v_snd_4033_, v___y_146217__boxed_4053_, v_fst_4035_, v_e_4036_, v_f_4037_, v___y_146218__boxed_4054_, v___x_4039_, v_____r_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___x_4039_);
lean_dec_ref(v___x_4030_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6___boxed(lean_object** _args){
lean_object* v_e_4056_ = _args[0];
lean_object* v___y_4057_ = _args[1];
lean_object* v_x_4058_ = _args[2];
lean_object* v_x_4059_ = _args[3];
lean_object* v_x_4060_ = _args[4];
lean_object* v___y_4061_ = _args[5];
lean_object* v___y_4062_ = _args[6];
lean_object* v___y_4063_ = _args[7];
lean_object* v___y_4064_ = _args[8];
lean_object* v___y_4065_ = _args[9];
lean_object* v___y_4066_ = _args[10];
lean_object* v___y_4067_ = _args[11];
lean_object* v___y_4068_ = _args[12];
lean_object* v___y_4069_ = _args[13];
lean_object* v___y_4070_ = _args[14];
lean_object* v___y_4071_ = _args[15];
lean_object* v___y_4072_ = _args[16];
_start:
{
uint8_t v___y_146317__boxed_4073_; lean_object* v_res_4074_; 
v___y_146317__boxed_4073_ = lean_unbox(v___y_4057_);
v_res_4074_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__6(v_e_4056_, v___y_146317__boxed_4073_, v_x_4058_, v_x_4059_, v_x_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0(lean_object* v_00_u03b2_4075_, lean_object* v_m_4076_, lean_object* v_a_4077_, lean_object* v_b_4078_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0___redArg(v_m_4076_, v_a_4077_, v_b_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1(lean_object* v_00_u03b2_4080_, lean_object* v_m_4081_, lean_object* v_a_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___redArg(v_m_4081_, v_a_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1___boxed(lean_object* v_00_u03b2_4084_, lean_object* v_m_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1(v_00_u03b2_4084_, v_m_4085_, v_a_4086_);
lean_dec_ref(v_a_4086_);
lean_dec_ref(v_m_4085_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3(lean_object* v_cls_4088_, lean_object* v_msg_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___redArg(v_cls_4088_, v_msg_4089_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3___boxed(lean_object* v_cls_4103_, lean_object* v_msg_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__3(v_cls_4103_, v_msg_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec(v___y_4105_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4(lean_object* v_upperBound_4118_, lean_object* v___x_4119_, uint8_t v___y_4120_, lean_object* v___x_4121_, lean_object* v_e_4122_, lean_object* v_f_4123_, uint8_t v___y_4124_, lean_object* v_inst_4125_, lean_object* v_R_4126_, lean_object* v_a_4127_, lean_object* v_b_4128_, lean_object* v_c_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; 
v___x_4142_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___redArg(v_upperBound_4118_, v___y_4120_, v___x_4121_, v_e_4122_, v_f_4123_, v___y_4124_, v_a_4127_, v_b_4128_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_4143_ = _args[0];
lean_object* v___x_4144_ = _args[1];
lean_object* v___y_4145_ = _args[2];
lean_object* v___x_4146_ = _args[3];
lean_object* v_e_4147_ = _args[4];
lean_object* v_f_4148_ = _args[5];
lean_object* v___y_4149_ = _args[6];
lean_object* v_inst_4150_ = _args[7];
lean_object* v_R_4151_ = _args[8];
lean_object* v_a_4152_ = _args[9];
lean_object* v_b_4153_ = _args[10];
lean_object* v_c_4154_ = _args[11];
lean_object* v___y_4155_ = _args[12];
lean_object* v___y_4156_ = _args[13];
lean_object* v___y_4157_ = _args[14];
lean_object* v___y_4158_ = _args[15];
lean_object* v___y_4159_ = _args[16];
lean_object* v___y_4160_ = _args[17];
lean_object* v___y_4161_ = _args[18];
lean_object* v___y_4162_ = _args[19];
lean_object* v___y_4163_ = _args[20];
lean_object* v___y_4164_ = _args[21];
lean_object* v___y_4165_ = _args[22];
lean_object* v___y_4166_ = _args[23];
_start:
{
uint8_t v___y_147357__boxed_4167_; uint8_t v___y_147359__boxed_4168_; lean_object* v_res_4169_; 
v___y_147357__boxed_4167_ = lean_unbox(v___y_4145_);
v___y_147359__boxed_4168_ = lean_unbox(v___y_4149_);
v_res_4169_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__4(v_upperBound_4143_, v___x_4144_, v___y_147357__boxed_4167_, v___x_4146_, v_e_4147_, v_f_4148_, v___y_147359__boxed_4168_, v_inst_4150_, v_R_4151_, v_a_4152_, v_b_4153_, v_c_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
lean_dec_ref(v___x_4146_);
lean_dec(v___x_4144_);
lean_dec(v_upperBound_4143_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5(lean_object* v_00_u03b2_4170_, lean_object* v_x_4171_, lean_object* v_x_4172_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___redArg(v_x_4171_, v_x_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5___boxed(lean_object* v_00_u03b2_4174_, lean_object* v_x_4175_, lean_object* v_x_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5(v_00_u03b2_4174_, v_x_4175_, v_x_4176_);
lean_dec_ref(v_x_4176_);
return v_res_4177_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0(lean_object* v_00_u03b2_4178_, lean_object* v_a_4179_, lean_object* v_x_4180_){
_start:
{
uint8_t v___x_4181_; 
v___x_4181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___redArg(v_a_4179_, v_x_4180_);
return v___x_4181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4182_, lean_object* v_a_4183_, lean_object* v_x_4184_){
_start:
{
uint8_t v_res_4185_; lean_object* v_r_4186_; 
v_res_4185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__0(v_00_u03b2_4182_, v_a_4183_, v_x_4184_);
lean_dec(v_x_4184_);
lean_dec_ref(v_a_4183_);
v_r_4186_ = lean_box(v_res_4185_);
return v_r_4186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1(lean_object* v_00_u03b2_4187_, lean_object* v_data_4188_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1___redArg(v_data_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__2(lean_object* v_00_u03b2_4190_, lean_object* v_a_4191_, lean_object* v_b_4192_, lean_object* v_x_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__2___redArg(v_a_4191_, v_b_4192_, v_x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4(lean_object* v_00_u03b2_4195_, lean_object* v_a_4196_, lean_object* v_x_4197_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___redArg(v_a_4196_, v_x_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4199_, lean_object* v_a_4200_, lean_object* v_x_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__1_spec__4(v_00_u03b2_4199_, v_a_4200_, v_x_4201_);
lean_dec(v_x_4201_);
lean_dec_ref(v_a_4200_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9(lean_object* v_00_u03b2_4203_, lean_object* v_x_4204_, size_t v_x_4205_, lean_object* v_x_4206_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___redArg(v_x_4204_, v_x_4205_, v_x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9___boxed(lean_object* v_00_u03b2_4208_, lean_object* v_x_4209_, lean_object* v_x_4210_, lean_object* v_x_4211_){
_start:
{
size_t v_x_147436__boxed_4212_; lean_object* v_res_4213_; 
v_x_147436__boxed_4212_ = lean_unbox_usize(v_x_4210_);
lean_dec(v_x_4210_);
v_res_4213_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9(v_00_u03b2_4208_, v_x_4209_, v_x_147436__boxed_4212_, v_x_4211_);
lean_dec_ref(v_x_4211_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4214_, lean_object* v_i_4215_, lean_object* v_source_4216_, lean_object* v_target_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4___redArg(v_i_4215_, v_source_4216_, v_target_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_4219_, lean_object* v_keys_4220_, lean_object* v_vals_4221_, lean_object* v_heq_4222_, lean_object* v_i_4223_, lean_object* v_k_4224_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___redArg(v_keys_4220_, v_vals_4221_, v_i_4223_, v_k_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b2_4226_, lean_object* v_keys_4227_, lean_object* v_vals_4228_, lean_object* v_heq_4229_, lean_object* v_i_4230_, lean_object* v_k_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__5_spec__9_spec__12(v_00_u03b2_4226_, v_keys_4227_, v_vals_4228_, v_heq_4229_, v_i_4230_, v_k_4231_);
lean_dec_ref(v_k_4231_);
lean_dec_ref(v_vals_4228_);
lean_dec_ref(v_keys_4227_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_4233_, lean_object* v_x_4234_, lean_object* v_x_4235_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit_spec__0_spec__1_spec__4_spec__10___redArg(v_x_4234_, v_x_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___redArg(lean_object* v_category_4237_, lean_object* v_opts_4238_, lean_object* v_act_4239_, lean_object* v_decl_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_apply_10(v_act_4239_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
v___x_4253_ = l_Lean_profileitIOUnsafe___redArg(v_category_4237_, v_opts_4238_, v___x_4252_, v_decl_4240_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___redArg___boxed(lean_object* v_category_4254_, lean_object* v_opts_4255_, lean_object* v_act_4256_, lean_object* v_decl_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___redArg(v_category_4254_, v_opts_4255_, v_act_4256_, v_decl_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
lean_dec_ref(v_opts_4255_);
lean_dec_ref(v_category_4254_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0(lean_object* v_00_u03b1_4270_, lean_object* v_category_4271_, lean_object* v_opts_4272_, lean_object* v_act_4273_, lean_object* v_decl_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___redArg(v_category_4271_, v_opts_4272_, v_act_4273_, v_decl_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___boxed(lean_object* v_00_u03b1_4287_, lean_object* v_category_4288_, lean_object* v_opts_4289_, lean_object* v_act_4290_, lean_object* v_decl_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0(v_00_u03b1_4287_, v_category_4288_, v_opts_4289_, v_act_4290_, v_decl_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
lean_dec_ref(v_opts_4289_);
lean_dec_ref(v_category_4288_);
return v_res_4303_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4304_ = lean_box(0);
v___x_4305_ = lean_unsigned_to_nat(16u);
v___x_4306_ = lean_mk_array(v___x_4305_, v___x_4304_);
return v___x_4306_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = lean_obj_once(&l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__0);
v___x_4308_ = lean_unsigned_to_nat(0u);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
lean_ctor_set(v___x_4309_, 1, v___x_4307_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl___lam__0(lean_object* v___x_4310_, lean_object* v_e_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___x_4346_; lean_object* v_a_4347_; uint8_t v___x_4348_; 
lean_inc(v___x_4310_);
v___x_4346_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__1___redArg(v___x_4310_, v___y_4320_);
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref(v___x_4346_);
v___x_4348_ = lean_unbox(v_a_4347_);
lean_dec(v_a_4347_);
if (v___x_4348_ == 0)
{
lean_dec(v___x_4310_);
v___y_4324_ = v___y_4312_;
v___y_4325_ = v___y_4313_;
v___y_4326_ = v___y_4314_;
v___y_4327_ = v___y_4315_;
v___y_4328_ = v___y_4316_;
v___y_4329_ = v___y_4317_;
v___y_4330_ = v___y_4318_;
v___y_4331_ = v___y_4319_;
v___y_4332_ = v___y_4320_;
v___y_4333_ = v___y_4321_;
goto v___jp_4323_;
}
else
{
lean_object* v___x_4349_; 
v___x_4349_ = l_Lean_Meta_Grind_updateLastTag(v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
lean_dec_ref(v___x_4349_);
lean_inc_ref(v_e_4311_);
v___x_4350_ = l_Lean_MessageData_ofExpr(v_e_4311_);
v___x_4351_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq_spec__2___redArg(v___x_4310_, v___x_4350_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_dec_ref(v___x_4351_);
v___y_4324_ = v___y_4312_;
v___y_4325_ = v___y_4313_;
v___y_4326_ = v___y_4314_;
v___y_4327_ = v___y_4315_;
v___y_4328_ = v___y_4316_;
v___y_4329_ = v___y_4317_;
v___y_4330_ = v___y_4318_;
v___y_4331_ = v___y_4319_;
v___y_4332_ = v___y_4320_;
v___y_4333_ = v___y_4321_;
goto v___jp_4323_;
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v_e_4311_);
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
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
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v_e_4311_);
lean_dec(v___x_4310_);
v_a_4360_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4349_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4349_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
v___jp_4323_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = lean_obj_once(&l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Canon_canonImpl___lam__0___closed__1);
v___x_4335_ = lean_st_mk_ref(v___x_4334_);
lean_inc(v___x_4335_);
v___x_4336_ = l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonImpl_visit(v_e_4311_, v___x_4335_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4345_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4341_ = lean_st_ref_get(v___x_4335_);
lean_dec(v___x_4335_);
lean_dec(v___x_4341_);
if (v_isShared_4340_ == 0)
{
v___x_4343_ = v___x_4339_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4337_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
else
{
lean_dec(v___x_4335_);
return v___x_4336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl___lam__0___boxed(lean_object* v___x_4368_, lean_object* v_e_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_Meta_Grind_Canon_canonImpl___lam__0(v___x_4368_, v_e_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* lean_grind_canon(lean_object* v_e_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v_options_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___f_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v_options_4395_ = lean_ctor_get(v_a_4392_, 2);
lean_inc_ref(v_options_4395_);
v___x_4396_ = ((lean_object*)(l_Lean_Meta_Grind_Canon_canonImpl___closed__0));
v___x_4397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_canonElemCore_checkDefEq___closed__3));
v___f_4398_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Canon_canonImpl___lam__0___boxed), 13, 2);
lean_closure_set(v___f_4398_, 0, v___x_4397_);
lean_closure_set(v___f_4398_, 1, v_e_4383_);
v___x_4399_ = lean_box(0);
v___x_4400_ = l_Lean_profileitM___at___00Lean_Meta_Grind_Canon_canonImpl_spec__0___redArg(v___x_4396_, v_options_4395_, v___f_4398_, v___x_4399_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_);
lean_dec_ref(v_options_4395_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Canon_canonImpl___boxed(lean_object* v_e_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = lean_grind_canon(v_e_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_);
return v_res_4413_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult_default = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult_default();
l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult = _init_l___private_Lean_Meta_Tactic_Grind_Canon_0__Lean_Meta_Grind_Canon_instInhabitedShouldCanonResult();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Canon(builtin);
}
#ifdef __cplusplus
}
#endif
