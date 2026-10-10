// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.CbvSimproc
// Imports: public import Lean.Compiler.InitAttr public import Lean.ScopedEnvExtension public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Simp.Result public import Lean.Meta.Sym.Simp.App public import Lean.Meta.Sym.Simp.DiscrTree public import Lean.Meta.Sym.Pattern
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_initializing();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Tactic.Cbv.CbvSimprocPhase.pre"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Cbv.CbvSimprocPhase.eval"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Tactic.Cbv.CbvSimprocPhase.post"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CbvSimprocPhase"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(174, 198, 190, 17, 0, 62, 186, 92)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(136, 145, 164, 233, 233, 175, 160, 110)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "post"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(119, 117, 11, 53, 165, 217, 228, 6)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 16, 153, 141, 221, 202, 206, 69)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase;
static const lean_array_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs;
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "Invalid builtin cbv simproc declaration: It can only be registered during initialization"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Invalid builtin cbv simproc declaration `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`: It has already been declared"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cbvSimprocDeclExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 182, 205, 129, 188, 54, 74, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Invalid cbv simproc declaration `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: It is declared in an imported module"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Cbv simproc `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "` has an unexpected type: Expected `Simproc`, but found `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cbvSimprocExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 184, 164, 42, 54, 246, 220, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not have a [cbv_simproc] attribute"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Invalid `[cbv_simproc]` attribute: `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a cbv simproc"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocEval"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 221, 189, 14, 79, 87, 225, 132)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbvSimprocAttr"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 104, 242, 136, 13, 73, 193, 222)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Invalid `[builtin_cbv_simproc]` attribute: `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` is not a builtin cbv simproc"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "addCbvSimprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 46, 19, 141, 119, 105, 81, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 144, 236, 69, 149, 78, 215, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CbvSimproc"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 246, 233, 32, 144, 0, 48, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(111, 195, 33, 67, 227, 201, 233, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 80, 153, 5, 12, 193, 47, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(86, 121, 100, 52, 100, 248, 58, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 62, 250, 213, 135, 222, 83)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(213, 6, 85, 205, 253, 185, 83, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 49, 121, 44, 210, 159, 116, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 89, 200, 112, 232, 34, 102, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 228, 129, 159, 189, 107, 203, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 188, 21, 86, 205, 70, 6, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 176, 116, 134, 116, 89, 199, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(31, 64, 46, 173, 247, 116, 204, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 173, 236, 92, 177, 72, 11, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)(((size_t)(735115364) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(127, 15, 195, 174, 145, 172, 96, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(20, 75, 147, 248, 238, 192, 151, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(64, 247, 227, 4, 148, 191, 156, 205)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(113, 151, 92, 207, 210, 188, 39, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Cbv simplification procedure"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Not implemented yet, [-builtin_cbv_simproc]"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cbvSimprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 176, 240, 9, 13, 93, 32, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Builtin cbv simplification procedure"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simproc "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ": done"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": no change"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n==>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simprocs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 69, 90, 123, 228, 205, 71, 22)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(lean_object* v_pre_24_){
_start:
{
lean_inc(v_pre_24_);
return v_pre_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg___boxed(lean_object* v_pre_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(v_pre_25_);
lean_dec(v_pre_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_pre_30_){
_start:
{
lean_inc(v_pre_30_);
return v_pre_30_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_pre_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(lean_box(0), v_t_28_, lean_box(0), v_pre_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_pre_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_pre_35_);
lean_dec(v_pre_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(lean_object* v_eval_38_){
_start:
{
lean_inc(v_eval_38_);
return v_eval_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg___boxed(lean_object* v_eval_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(v_eval_39_);
lean_dec(v_eval_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_eval_44_){
_start:
{
lean_inc(v_eval_44_);
return v_eval_44_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_eval_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(lean_box(0), v_t_42_, lean_box(0), v_eval_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_eval_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_eval_49_);
lean_dec(v_eval_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(lean_object* v_post_52_){
_start:
{
lean_inc(v_post_52_);
return v_post_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg___boxed(lean_object* v_post_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(v_post_53_);
lean_dec(v_post_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_post_58_){
_start:
{
lean_inc(v_post_58_);
return v_post_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_post_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(lean_box(0), v_t_56_, lean_box(0), v_post_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_post_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_post_63_);
lean_dec(v_post_63_);
return v_res_65_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default(void){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(uint8_t v_x_68_, uint8_t v_y_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_70_ = lean_box(v_x_68_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_box(v_y_69_);
v___x_73_ = lean_obj_tag_nat(v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_nat_dec_eq(v___x_71_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_68_ = stack[0].m_num;
uint8_t v_y_69_ = stack[1].m_num;
uint8_t v_res_75_;
v_res_75_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(v_x_68_, v_y_69_);
stack->m_num = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed(lean_object* v_x_76_, lean_object* v_y_77_){
_start:
{
uint8_t v_x_24__boxed_78_; uint8_t v_y_25__boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_x_24__boxed_78_ = lean_unbox(v_x_76_);
v_y_25__boxed_79_ = lean_unbox(v_y_77_);
v_res_80_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(v_x_24__boxed_78_, v_y_25__boxed_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
uint64_t l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(uint8_t v_x_84_){
_start:
{
switch(v_x_84_)
{
case 0:
{
uint64_t v___x_85_; 
v___x_85_ = 0ULL;
return v___x_85_;
}
case 1:
{
uint64_t v___x_86_; 
v___x_86_ = 1ULL;
return v___x_86_;
}
default: 
{
uint64_t v___x_87_; 
v___x_87_ = 2ULL;
return v___x_87_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_84_ = stack[0].m_num;
uint64_t v_res_88_;
v_res_88_ = l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(v_x_84_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed(lean_object* v_x_89_){
_start:
{
uint8_t v_x_40__boxed_90_; uint64_t v_res_91_; lean_object* v_r_92_; 
v_x_40__boxed_90_ = lean_unbox(v_x_89_);
v_res_91_ = l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(v_x_40__boxed_90_);
v_r_92_ = lean_box_uint64(v_res_91_);
return v_r_92_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(2u);
v___x_105_ = lean_nat_to_int(v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_to_int(v___x_106_);
return v___x_107_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(uint8_t v_x_108_, lean_object* v_prec_109_){
_start:
{
lean_object* v___y_111_; lean_object* v___y_118_; lean_object* v___y_125_; 
switch(v_x_108_)
{
case 0:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1024u);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_prec_109_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_111_ = v___x_133_;
goto v___jp_110_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_111_ = v___x_134_;
goto v___jp_110_;
}
}
case 1:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = lean_nat_dec_le(v___x_135_, v_prec_109_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_118_ = v___x_137_;
goto v___jp_117_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_118_ = v___x_138_;
goto v___jp_117_;
}
}
default: 
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(1024u);
v___x_140_ = lean_nat_dec_le(v___x_139_, v_prec_109_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_125_ = v___x_141_;
goto v___jp_124_;
}
else
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_125_ = v___x_142_;
goto v___jp_124_;
}
}
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1));
lean_inc(v___y_111_);
v___x_113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_113_, 0, v___y_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = 0;
v___x_115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_114_);
v___x_116_ = l_Repr_addAppParen(v___x_115_, v_prec_109_);
return v___x_116_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_119_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3));
lean_inc(v___y_118_);
v___x_120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_120_, 0, v___y_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = 0;
v___x_122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___x_121_);
v___x_123_ = l_Repr_addAppParen(v___x_122_, v_prec_109_);
return v___x_123_;
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5));
lean_inc(v___y_125_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = 0;
v___x_129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = l_Repr_addAppParen(v___x_129_, v_prec_109_);
return v___x_130_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_108_ = stack[0].m_num;
lean_object* v_prec_109_ = stack[1].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(v_x_108_, v_prec_109_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed(lean_object* v_x_144_, lean_object* v_prec_145_){
_start:
{
uint8_t v_x_171__boxed_146_; lean_object* v_res_147_; 
v_x_171__boxed_146_ = lean_unbox(v_x_144_);
v_res_147_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(v_x_171__boxed_146_, v_prec_145_);
lean_dec(v_prec_145_);
return v_res_147_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_box(0);
v___x_164_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6));
v___x_165_ = l_Lean_mkConst(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_box(0);
v___x_175_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9));
v___x_176_ = l_Lean_mkConst(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_box(0);
v___x_186_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12));
v___x_187_ = l_Lean_mkConst(v___x_186_, v___x_185_);
return v___x_187_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(uint8_t v_x_188_){
_start:
{
switch(v_x_188_)
{
case 0:
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
return v___x_189_;
}
case 1:
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
return v___x_190_;
}
default: 
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
return v___x_191_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_188_ = stack[0].m_num;
lean_object* v_res_192_;
v_res_192_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(v_x_188_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed(lean_object* v_x_193_){
_start:
{
uint8_t v_x_196__boxed_194_; lean_object* v_res_195_; 
v_x_196__boxed_194_ = lean_unbox(v_x_193_);
v_res_195_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(v_x_196__boxed_194_);
return v_res_195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_box(0);
v___x_204_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1));
v___x_205_ = l_Lean_mkConst(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3(void){
_start:
{
lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2);
v___f_207_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0));
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___f_207_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase(void){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3);
return v___x_209_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(lean_object* v_e_u2081_218_, lean_object* v_e_u2082_219_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_220_; lean_object* v_toCbvSimprocOLeanEntry_221_; lean_object* v_declName_222_; lean_object* v_declName_223_; uint8_t v___x_224_; 
v_toCbvSimprocOLeanEntry_220_ = lean_ctor_get(v_e_u2081_218_, 0);
v_toCbvSimprocOLeanEntry_221_ = lean_ctor_get(v_e_u2082_219_, 0);
v_declName_222_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_220_, 0);
v_declName_223_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_221_, 0);
v___x_224_ = lean_name_eq(v_declName_222_, v_declName_223_);
return v___x_224_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_218_ = stack[0].m_obj;
lean_object* v_e_u2082_219_ = stack[1].m_obj;
uint8_t v_res_225_;
v_res_225_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(v_e_u2081_218_, v_e_u2082_219_);
stack->m_num = v_res_225_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed(lean_object* v_e_u2081_226_, lean_object* v_e_u2082_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(v_e_u2081_226_, v_e_u2082_227_);
lean_dec_ref(v_e_u2082_227_);
lean_dec_ref(v_e_u2081_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0(lean_object* v_e_232_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_233_; lean_object* v_declName_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_toCbvSimprocOLeanEntry_233_ = lean_ctor_get(v_e_232_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_233_);
lean_dec_ref(v_e_232_);
v_declName_234_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_233_, 0);
lean_inc(v_declName_234_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_233_);
v___x_235_ = 1;
v___x_236_ = l_Lean_Name_toString(v_declName_234_, v___x_235_);
v___x_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_240_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg(){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__1);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_245_;
v_res_245_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg();
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___boxed(lean_object* v___dummy_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg();
return v_res_247_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg();
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_object* v_00_u03b2_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0);
v___x_254_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0);
v___x_255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set(v___x_255_, 2, v___x_254_);
lean_ctor_set(v___x_255_, 3, v___x_253_);
lean_ctor_set(v___x_255_, 4, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(lean_object* v_xs_258_, lean_object* v_v_259_, lean_object* v_i_260_){
_start:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_array_get_size(v_xs_258_);
v___x_262_ = lean_nat_dec_lt(v_i_260_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec(v_i_260_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
else
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_array_fget_borrowed(v_xs_258_, v_i_260_);
v___x_265_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_264_, v_v_259_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_add(v_i_260_, v___x_266_);
lean_dec(v_i_260_);
v_i_260_ = v___x_267_;
goto _start;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_i_260_);
return v___x_269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19___boxed(lean_object* v_xs_270_, lean_object* v_v_271_, lean_object* v_i_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(v_xs_270_, v_v_271_, v_i_272_);
lean_dec(v_v_271_);
lean_dec_ref(v_xs_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(lean_object* v_xs_274_, lean_object* v_v_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12_spec__19(v_xs_274_, v_v_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12___boxed(lean_object* v_xs_278_, lean_object* v_v_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(v_xs_278_, v_v_279_);
lean_dec(v_v_279_);
lean_dec_ref(v_xs_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21_spec__22___redArg(lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_ks_285_; lean_object* v_vs_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_310_; 
v_ks_285_ = lean_ctor_get(v_x_281_, 0);
v_vs_286_ = lean_ctor_get(v_x_281_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_310_ == 0)
{
v___x_288_ = v_x_281_;
v_isShared_289_ = v_isSharedCheck_310_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_vs_286_);
lean_inc(v_ks_285_);
lean_dec(v_x_281_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_310_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_ks_285_);
v___x_291_ = lean_nat_dec_lt(v_x_282_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec(v_x_282_);
v___x_292_ = lean_array_push(v_ks_285_, v_x_283_);
v___x_293_ = lean_array_push(v_vs_286_, v_x_284_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_293_);
lean_ctor_set(v___x_288_, 0, v___x_292_);
v___x_295_ = v___x_288_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
lean_object* v_k_x27_297_; uint8_t v___x_298_; 
v_k_x27_297_ = lean_array_fget_borrowed(v_ks_285_, v_x_282_);
v___x_298_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_283_, v_k_x27_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_300_; 
if (v_isShared_289_ == 0)
{
v___x_300_ = v___x_288_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_ks_285_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_vs_286_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_x_282_, v___x_301_);
lean_dec(v_x_282_);
v_x_281_ = v___x_300_;
v_x_282_ = v___x_302_;
goto _start;
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_305_ = lean_array_fset(v_ks_285_, v_x_282_, v_x_283_);
v___x_306_ = lean_array_fset(v_vs_286_, v_x_282_, v_x_284_);
lean_dec(v_x_282_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_306_);
lean_ctor_set(v___x_288_, 0, v___x_305_);
v___x_308_ = v___x_288_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21___redArg(lean_object* v_n_311_, lean_object* v_k_312_, lean_object* v_v_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21_spec__22___redArg(v_n_311_, v___x_314_, v_k_312_, v_v_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_316_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(lean_object* v_x_317_, size_t v_x_318_, size_t v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v_es_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v_j_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_es_322_ = lean_ctor_get(v_x_317_, 0);
v___x_323_ = ((size_t)31ULL);
v___x_324_ = lean_usize_land(v_x_318_, v___x_323_);
v_j_325_ = lean_usize_to_nat(v___x_324_);
v___x_326_ = lean_array_get_size(v_es_322_);
v___x_327_ = lean_nat_dec_lt(v_j_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_dec(v_j_325_);
lean_dec(v_x_321_);
lean_dec(v_x_320_);
return v_x_317_;
}
else
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_es_322_);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_317_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_x_317_, 0);
lean_dec(v_unused_367_);
v___x_329_ = v_x_317_;
v_isShared_330_ = v_isSharedCheck_366_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_x_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_366_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_v_331_; lean_object* v___x_332_; lean_object* v_xs_x27_333_; lean_object* v___y_335_; 
v_v_331_ = lean_array_fget(v_es_322_, v_j_325_);
v___x_332_ = lean_box(0);
v_xs_x27_333_ = lean_array_fset(v_es_322_, v_j_325_, v___x_332_);
switch(lean_obj_tag(v_v_331_))
{
case 0:
{
lean_object* v_key_340_; lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_351_; 
v_key_340_ = lean_ctor_get(v_v_331_, 0);
v_val_341_ = lean_ctor_get(v_v_331_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_v_331_);
if (v_isSharedCheck_351_ == 0)
{
v___x_343_ = v_v_331_;
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_inc(v_key_340_);
lean_dec(v_v_331_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint8_t v___x_345_; 
v___x_345_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_320_, v_key_340_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_del_object(v___x_343_);
v___x_346_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_340_, v_val_341_, v_x_320_, v_x_321_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___y_335_ = v___x_347_;
goto v___jp_334_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_val_341_);
lean_dec(v_key_340_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v_x_321_);
lean_ctor_set(v___x_343_, 0, v_x_320_);
v___x_349_ = v___x_343_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_x_320_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_x_321_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v___y_335_ = v___x_349_;
goto v___jp_334_;
}
}
}
}
case 1:
{
lean_object* v_node_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_364_; 
v_node_352_ = lean_ctor_get(v_v_331_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_v_331_);
if (v_isSharedCheck_364_ == 0)
{
v___x_354_ = v_v_331_;
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_node_352_);
lean_dec(v_v_331_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_356_ = ((size_t)5ULL);
v___x_357_ = lean_usize_shift_right(v_x_318_, v___x_356_);
v___x_358_ = ((size_t)1ULL);
v___x_359_ = lean_usize_add(v_x_319_, v___x_358_);
v___x_360_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(v_node_352_, v___x_357_, v___x_359_, v_x_320_, v_x_321_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_360_);
v___x_362_ = v___x_354_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v___y_335_ = v___x_362_;
goto v___jp_334_;
}
}
}
default: 
{
lean_object* v___x_365_; 
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_x_320_);
lean_ctor_set(v___x_365_, 1, v_x_321_);
v___y_335_ = v___x_365_;
goto v___jp_334_;
}
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_array_fset(v_xs_x27_333_, v_j_325_, v___y_335_);
lean_dec(v_j_325_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_336_);
v___x_338_ = v___x_329_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
else
{
lean_object* v_ks_368_; lean_object* v_vs_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_387_; 
v_ks_368_ = lean_ctor_get(v_x_317_, 0);
v_vs_369_ = lean_ctor_get(v_x_317_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_317_);
if (v_isSharedCheck_387_ == 0)
{
v___x_371_ = v_x_317_;
v_isShared_372_ = v_isSharedCheck_387_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_vs_369_);
lean_inc(v_ks_368_);
lean_dec(v_x_317_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_387_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_ks_368_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_vs_369_);
v___x_374_ = v_reuseFailAlloc_386_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v_newNode_375_; size_t v___x_376_; uint8_t v___x_377_; 
v_newNode_375_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21___redArg(v___x_374_, v_x_320_, v_x_321_);
v___x_376_ = ((size_t)7ULL);
v___x_377_ = lean_usize_dec_le(v___x_376_, v_x_319_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_375_);
v___x_379_ = lean_unsigned_to_nat(4u);
v___x_380_ = lean_nat_dec_lt(v___x_378_, v___x_379_);
lean_dec(v___x_378_);
if (v___x_380_ == 0)
{
lean_object* v_ks_381_; lean_object* v_vs_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_ks_381_ = lean_ctor_get(v_newNode_375_, 0);
lean_inc_ref(v_ks_381_);
v_vs_382_ = lean_ctor_get(v_newNode_375_, 1);
lean_inc_ref(v_vs_382_);
lean_dec_ref(v_newNode_375_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0);
v___x_385_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg(v_x_319_, v_ks_381_, v_vs_382_, v___x_383_, v___x_384_);
lean_dec_ref(v_vs_382_);
lean_dec_ref(v_ks_381_);
return v___x_385_;
}
else
{
return v_newNode_375_;
}
}
else
{
return v_newNode_375_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_317_ = stack[0].m_obj;
size_t v_x_318_ = stack[1].m_num;
size_t v_x_319_ = stack[2].m_num;
lean_object* v_x_320_ = stack[3].m_obj;
lean_object* v_x_321_ = stack[4].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(v_x_317_, v_x_318_, v_x_319_, v_x_320_, v_x_321_);
stack->m_obj
 = v_res_388_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg(size_t v_depth_389_, lean_object* v_keys_390_, lean_object* v_vals_391_, lean_object* v_i_392_, lean_object* v_entries_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_get_size(v_keys_390_);
v___x_395_ = lean_nat_dec_lt(v_i_392_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec(v_i_392_);
return v_entries_393_;
}
else
{
lean_object* v_k_396_; lean_object* v_v_397_; uint64_t v___x_398_; size_t v_h_399_; size_t v___x_400_; lean_object* v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v_h_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_k_396_ = lean_array_fget_borrowed(v_keys_390_, v_i_392_);
v_v_397_ = lean_array_fget_borrowed(v_vals_391_, v_i_392_);
v___x_398_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_396_);
v_h_399_ = lean_uint64_to_usize(v___x_398_);
v___x_400_ = ((size_t)5ULL);
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_sub(v_depth_389_, v___x_402_);
v___x_404_ = lean_usize_mul(v___x_400_, v___x_403_);
v_h_405_ = lean_usize_shift_right(v_h_399_, v___x_404_);
v___x_406_ = lean_nat_add(v_i_392_, v___x_401_);
lean_dec(v_i_392_);
lean_inc(v_v_397_);
lean_inc(v_k_396_);
v___x_407_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(v_entries_393_, v_h_405_, v_depth_389_, v_k_396_, v_v_397_);
v_i_392_ = v___x_406_;
v_entries_393_ = v___x_407_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_389_ = stack[0].m_num;
lean_object* v_keys_390_ = stack[1].m_obj;
lean_object* v_vals_391_ = stack[2].m_obj;
lean_object* v_i_392_ = stack[3].m_obj;
lean_object* v_entries_393_ = stack[4].m_obj;
lean_object* v_res_409_;
v_res_409_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg(v_depth_389_, v_keys_390_, v_vals_391_, v_i_392_, v_entries_393_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg___boxed(lean_object* v_depth_410_, lean_object* v_keys_411_, lean_object* v_vals_412_, lean_object* v_i_413_, lean_object* v_entries_414_){
_start:
{
size_t v_depth_boxed_415_; lean_object* v_res_416_; 
v_depth_boxed_415_ = lean_unbox_usize(v_depth_410_);
lean_dec(v_depth_410_);
v_res_416_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg(v_depth_boxed_415_, v_keys_411_, v_vals_412_, v_i_413_, v_entries_414_);
lean_dec_ref(v_vals_412_);
lean_dec_ref(v_keys_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___boxed(lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
size_t v_x_3184__boxed_422_; size_t v_x_3185__boxed_423_; lean_object* v_res_424_; 
v_x_3184__boxed_422_ = lean_unbox_usize(v_x_418_);
lean_dec(v_x_418_);
v_x_3185__boxed_423_ = lean_unbox_usize(v_x_419_);
lean_dec(v_x_419_);
v_res_424_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(v_x_417_, v_x_3184__boxed_422_, v_x_3185__boxed_423_, v_x_420_, v_x_421_);
return v_res_424_;
}
}
uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(lean_object* v_a_425_, lean_object* v_b_426_){
_start:
{
lean_object* v_fst_427_; lean_object* v_fst_428_; uint8_t v___x_429_; 
v_fst_427_ = lean_ctor_get(v_a_425_, 0);
v_fst_428_ = lean_ctor_get(v_b_426_, 0);
v___x_429_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_427_, v_fst_428_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_425_ = stack[0].m_obj;
lean_object* v_b_426_ = stack[1].m_obj;
uint8_t v_res_430_;
v_res_430_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_a_425_, v_b_426_);
stack->m_num = v_res_430_;
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0___boxed(lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_a_431_, v_b_432_);
lean_dec_ref(v_b_432_);
lean_dec_ref(v_a_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0(lean_object* v_x_435_, lean_object* v_keys_436_, lean_object* v_v_437_, lean_object* v_k_438_, lean_object* v_x_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_c_442_; lean_object* v___x_443_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_x_435_, v___x_440_);
v_c_442_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_436_, v_v_437_, v___x_441_);
lean_dec(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_k_438_);
lean_ctor_set(v___x_443_, 1, v_c_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0___boxed(lean_object* v_x_444_, lean_object* v_keys_445_, lean_object* v_v_446_, lean_object* v_k_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0(v_x_444_, v_keys_445_, v_v_446_, v_k_447_, v_x_448_);
lean_dec_ref(v_keys_445_);
lean_dec(v_x_444_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(lean_object* v_vs_450_, lean_object* v_v_451_, lean_object* v_i_452_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_get_size(v_vs_450_);
v___x_454_ = lean_nat_dec_lt(v_i_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v_i_452_);
v___x_455_ = lean_array_push(v_vs_450_, v_v_451_);
return v___x_455_;
}
else
{
lean_object* v_toCbvSimprocOLeanEntry_456_; lean_object* v_declName_457_; lean_object* v___x_458_; lean_object* v_toCbvSimprocOLeanEntry_459_; lean_object* v_declName_460_; uint8_t v___x_461_; 
v_toCbvSimprocOLeanEntry_456_ = lean_ctor_get(v_v_451_, 0);
v_declName_457_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_456_, 0);
v___x_458_ = lean_array_fget_borrowed(v_vs_450_, v_i_452_);
v_toCbvSimprocOLeanEntry_459_ = lean_ctor_get(v___x_458_, 0);
v_declName_460_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_459_, 0);
v___x_461_ = lean_name_eq(v_declName_457_, v_declName_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = lean_nat_add(v_i_452_, v___x_462_);
lean_dec(v_i_452_);
v_i_452_ = v___x_463_;
goto _start;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = lean_array_fset(v_vs_450_, v_i_452_, v_v_451_);
lean_dec(v_i_452_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(lean_object* v_vs_466_, lean_object* v_v_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9_spec__14(v_vs_466_, v_v_467_, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v___x_470_, lean_object* v_as_471_, lean_object* v_k_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_mid_477_; lean_object* v_midVal_478_; uint8_t v___x_479_; 
v___x_475_ = lean_nat_add(v_x_473_, v_x_474_);
v___x_476_ = lean_unsigned_to_nat(1u);
v_mid_477_ = lean_nat_shiftr(v___x_475_, v___x_476_);
lean_dec(v___x_475_);
v_midVal_478_ = lean_array_fget_borrowed(v_as_471_, v_mid_477_);
v___x_479_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_midVal_478_, v_k_472_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
lean_dec(v_x_474_);
v___x_480_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_k_472_, v_midVal_478_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
lean_dec(v_x_473_);
v___x_481_ = lean_array_get_size(v_as_471_);
v___x_482_ = lean_nat_dec_lt(v_mid_477_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec(v_mid_477_);
lean_dec_ref(v___x_470_);
return v_as_471_;
}
else
{
lean_object* v___x_483_; lean_object* v_xs_x27_484_; lean_object* v___x_485_; 
v___x_483_ = lean_box(0);
v_xs_x27_484_ = lean_array_fset(v_as_471_, v_mid_477_, v___x_483_);
v___x_485_ = lean_array_fset(v_xs_x27_484_, v_mid_477_, v___x_470_);
lean_dec(v_mid_477_);
return v___x_485_;
}
}
else
{
v_x_474_ = v_mid_477_;
goto _start;
}
}
else
{
uint8_t v___x_487_; 
v___x_487_ = lean_nat_dec_eq(v_mid_477_, v_x_473_);
if (v___x_487_ == 0)
{
lean_dec(v_x_473_);
v_x_473_ = v_mid_477_;
goto _start;
}
else
{
lean_object* v___x_489_; lean_object* v_j_490_; lean_object* v_as_491_; lean_object* v___x_492_; 
lean_dec(v_mid_477_);
lean_dec(v_x_474_);
v___x_489_ = lean_nat_add(v_x_473_, v___x_476_);
lean_dec(v_x_473_);
v_j_490_ = lean_array_get_size(v_as_471_);
v_as_491_ = lean_array_push(v_as_471_, v___x_470_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_489_, v_as_491_, v_j_490_);
lean_dec(v___x_489_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v___x_493_, lean_object* v_as_494_, lean_object* v_k_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v___x_493_, v_as_494_, v_k_495_, v_x_496_, v_x_497_);
lean_dec_ref(v_k_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object* v___x_499_, lean_object* v_as_500_, lean_object* v_k_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_array_get_size(v_as_500_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_nat_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_fget_borrowed(v_as_500_, v___x_503_);
v___x_506_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_k_501_, v___x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v___x_505_, v_k_501_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = lean_nat_dec_lt(v___x_503_, v___x_502_);
if (v___x_508_ == 0)
{
lean_dec_ref(v___x_499_);
return v_as_500_;
}
else
{
lean_object* v___x_509_; lean_object* v_xs_x27_510_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
v_xs_x27_510_ = lean_array_fset(v_as_500_, v___x_503_, v___x_509_);
v___x_511_ = lean_array_fset(v_xs_x27_510_, v___x_503_, v___x_499_);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_sub(v___x_502_, v___x_512_);
v___x_514_ = lean_array_fget_borrowed(v_as_500_, v___x_513_);
v___x_515_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v___x_514_, v_k_501_);
if (v___x_515_ == 0)
{
uint8_t v___x_516_; 
v___x_516_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_k_501_, v___x_514_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; 
v___x_517_ = lean_nat_dec_lt(v___x_513_, v___x_502_);
if (v___x_517_ == 0)
{
lean_dec(v___x_513_);
lean_dec_ref(v___x_499_);
return v_as_500_;
}
else
{
lean_object* v___x_518_; lean_object* v_xs_x27_519_; lean_object* v___x_520_; 
v___x_518_ = lean_box(0);
v_xs_x27_519_ = lean_array_fset(v_as_500_, v___x_513_, v___x_518_);
v___x_520_ = lean_array_fset(v_xs_x27_519_, v___x_513_, v___x_499_);
lean_dec(v___x_513_);
return v___x_520_;
}
}
else
{
lean_object* v___x_521_; 
v___x_521_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v___x_499_, v_as_500_, v_k_501_, v___x_503_, v___x_513_);
return v___x_521_;
}
}
else
{
lean_object* v___x_522_; 
lean_dec(v___x_513_);
v___x_522_ = lean_array_push(v_as_500_, v___x_499_);
return v___x_522_;
}
}
}
else
{
lean_object* v_as_523_; lean_object* v___x_524_; 
v_as_523_ = lean_array_push(v_as_500_, v___x_499_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_503_, v_as_523_, v___x_502_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_array_push(v_as_500_, v___x_499_);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___boxed(lean_object* v___x_526_, lean_object* v_as_527_, lean_object* v_k_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v___x_526_, v_as_527_, v_k_528_);
lean_dec_ref(v_k_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___redArg(lean_object* v_x_534_, lean_object* v_keys_535_, lean_object* v_v_536_, lean_object* v_k_537_, lean_object* v_as_538_, lean_object* v_k_539_, lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_mid_544_; lean_object* v_midVal_545_; uint8_t v___x_546_; 
v___x_542_ = lean_nat_add(v_x_540_, v_x_541_);
v___x_543_ = lean_unsigned_to_nat(1u);
v_mid_544_ = lean_nat_shiftr(v___x_542_, v___x_543_);
lean_dec(v___x_542_);
v_midVal_545_ = lean_array_fget(v_as_538_, v_mid_544_);
v___x_546_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_midVal_545_, v_k_539_);
if (v___x_546_ == 0)
{
uint8_t v___x_547_; 
lean_dec(v_x_541_);
v___x_547_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_k_539_, v_midVal_545_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; uint8_t v___x_549_; 
lean_dec(v_x_540_);
v___x_548_ = lean_array_get_size(v_as_538_);
v___x_549_ = lean_nat_dec_lt(v_mid_544_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec(v_midVal_545_);
lean_dec(v_mid_544_);
lean_dec(v_k_537_);
lean_dec_ref(v_v_536_);
return v_as_538_;
}
else
{
lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_562_; 
v_snd_550_ = lean_ctor_get(v_midVal_545_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_midVal_545_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_midVal_545_, 0);
lean_dec(v_unused_563_);
v___x_552_ = v_midVal_545_;
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_dec(v_midVal_545_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_xs_x27_555_; lean_object* v___x_556_; lean_object* v_c_557_; lean_object* v___x_559_; 
v___x_554_ = lean_box(0);
v_xs_x27_555_ = lean_array_fset(v_as_538_, v_mid_544_, v___x_554_);
v___x_556_ = lean_nat_add(v_x_534_, v___x_543_);
v_c_557_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_535_, v_v_536_, v___x_556_, v_snd_550_);
lean_dec(v___x_556_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_c_557_);
lean_ctor_set(v___x_552_, 0, v_k_537_);
v___x_559_ = v___x_552_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_c_557_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
v___x_560_ = lean_array_fset(v_xs_x27_555_, v_mid_544_, v___x_559_);
lean_dec(v_mid_544_);
return v___x_560_;
}
}
}
}
else
{
lean_dec(v_midVal_545_);
v_x_541_ = v_mid_544_;
goto _start;
}
}
else
{
uint8_t v___x_565_; 
lean_dec(v_midVal_545_);
v___x_565_ = lean_nat_dec_eq(v_mid_544_, v_x_540_);
if (v___x_565_ == 0)
{
lean_dec(v_x_540_);
v_x_540_ = v_mid_544_;
goto _start;
}
else
{
lean_object* v___x_567_; lean_object* v_c_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_j_571_; lean_object* v_as_572_; lean_object* v___x_573_; 
lean_dec(v_mid_544_);
lean_dec(v_x_541_);
v___x_567_ = lean_nat_add(v_x_534_, v___x_543_);
v_c_568_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_535_, v_v_536_, v___x_567_);
lean_dec(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_k_537_);
lean_ctor_set(v___x_569_, 1, v_c_568_);
v___x_570_ = lean_nat_add(v_x_540_, v___x_543_);
lean_dec(v_x_540_);
v_j_571_ = lean_array_get_size(v_as_538_);
v_as_572_ = lean_array_push(v_as_538_, v___x_569_);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_570_, v_as_572_, v_j_571_);
lean_dec(v___x_570_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10(lean_object* v_x_574_, lean_object* v_keys_575_, lean_object* v_v_576_, lean_object* v_k_577_, lean_object* v_as_578_, lean_object* v_k_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_array_get_size(v_as_578_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_array_fget_borrowed(v_as_578_, v___x_581_);
v___x_584_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_k_579_, v___x_583_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
v___x_585_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v___x_583_, v_k_579_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v___x_581_, v___x_580_);
if (v___x_586_ == 0)
{
lean_dec(v_k_577_);
lean_dec_ref(v_v_576_);
return v_as_578_;
}
else
{
lean_object* v___x_587_; lean_object* v_xs_x27_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_inc(v___x_583_);
v___x_587_ = lean_box(0);
v_xs_x27_588_ = lean_array_fset(v_as_578_, v___x_581_, v___x_587_);
v___x_589_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__2(v_x_574_, v_keys_575_, v_v_576_, v_k_577_, v___x_583_);
v___x_590_ = lean_array_fset(v_xs_x27_588_, v___x_581_, v___x_589_);
return v___x_590_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_sub(v___x_580_, v___x_591_);
v___x_593_ = lean_array_fget_borrowed(v_as_578_, v___x_592_);
v___x_594_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v___x_593_, v_k_579_);
if (v___x_594_ == 0)
{
uint8_t v___x_595_; 
v___x_595_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___lam__0(v_k_579_, v___x_593_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
v___x_596_ = lean_nat_dec_lt(v___x_592_, v___x_580_);
if (v___x_596_ == 0)
{
lean_dec(v___x_592_);
lean_dec(v_k_577_);
lean_dec_ref(v_v_576_);
return v_as_578_;
}
else
{
lean_object* v___x_597_; lean_object* v_xs_x27_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_inc(v___x_593_);
v___x_597_ = lean_box(0);
v_xs_x27_598_ = lean_array_fset(v_as_578_, v___x_592_, v___x_597_);
v___x_599_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__2(v_x_574_, v_keys_575_, v_v_576_, v_k_577_, v___x_593_);
v___x_600_ = lean_array_fset(v_xs_x27_598_, v___x_592_, v___x_599_);
lean_dec(v___x_592_);
return v___x_600_;
}
}
else
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___redArg(v_x_574_, v_keys_575_, v_v_576_, v_k_577_, v_as_578_, v_k_579_, v___x_581_, v___x_592_);
return v___x_601_;
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v___x_592_);
v___x_602_ = lean_box(0);
v___x_603_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0(v_x_574_, v_keys_575_, v_v_576_, v_k_577_, v___x_602_);
v___x_604_ = lean_array_push(v_as_578_, v___x_603_);
return v___x_604_;
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_as_607_; lean_object* v___x_608_; 
v___x_605_ = lean_box(0);
v___x_606_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0(v_x_574_, v_keys_575_, v_v_576_, v_k_577_, v___x_605_);
v_as_607_ = lean_array_push(v_as_578_, v___x_606_);
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_581_, v_as_607_, v___x_580_);
return v___x_608_;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
v___x_610_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__0(v_x_574_, v_keys_575_, v_v_576_, v_k_577_, v___x_609_);
v___x_611_ = lean_array_push(v_as_578_, v___x_610_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object* v_keys_612_, lean_object* v_v_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_key_616_; lean_object* v_child_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_651_; 
v_key_616_ = lean_ctor_get(v_x_615_, 0);
v_child_617_ = lean_ctor_get(v_x_615_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_651_ == 0)
{
v___x_619_ = v_x_615_;
v_isShared_620_ = v_isSharedCheck_651_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_child_617_);
lean_inc(v_key_616_);
lean_dec(v_x_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_651_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_keys_612_);
v___x_622_ = lean_nat_dec_lt(v_x_614_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_mk_empty_array_with_capacity(v___x_623_);
lean_inc_ref(v___x_624_);
v___x_625_ = lean_array_push(v___x_624_, v_v_613_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_key_616_);
lean_ctor_set(v___x_626_, 1, v_child_617_);
v___x_627_ = lean_array_push(v___x_624_, v___x_626_);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 1);
lean_ctor_set(v___x_619_, 1, v___x_627_);
lean_ctor_set(v___x_619_, 0, v___x_625_);
v___x_629_ = v___x_619_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_array_fget_borrowed(v_keys_612_, v_x_614_);
v___x_632_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_631_, v_key_616_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__0));
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_key_616_);
lean_ctor_set(v___x_634_, 1, v_child_617_);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_mk_empty_array_with_capacity(v___x_635_);
v___x_637_ = lean_array_push(v___x_636_, v___x_634_);
v___x_638_ = lean_nat_add(v_x_614_, v___x_635_);
v___x_639_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_612_, v_v_613_, v___x_638_);
lean_dec(v___x_638_);
lean_inc(v___x_631_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_631_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_inc_ref(v___x_640_);
v___x_641_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v___x_640_, v___x_637_, v___x_640_);
lean_dec_ref_known(v___x_640_, 2);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 1);
lean_ctor_set(v___x_619_, 1, v___x_641_);
lean_ctor_set(v___x_619_, 0, v___x_633_);
v___x_643_ = v___x_619_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_add(v_x_614_, v___x_645_);
v___x_647_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_612_, v_v_613_, v___x_646_, v_child_617_);
lean_dec(v___x_646_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_647_);
v___x_649_ = v___x_619_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_key_616_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v_vs_652_; lean_object* v_children_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_670_; 
v_vs_652_ = lean_ctor_get(v_x_615_, 0);
v_children_653_ = lean_ctor_get(v_x_615_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_670_ == 0)
{
v___x_655_ = v_x_615_;
v_isShared_656_ = v_isSharedCheck_670_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_children_653_);
lean_inc(v_vs_652_);
lean_dec(v_x_615_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_670_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_array_get_size(v_keys_612_);
v___x_658_ = lean_nat_dec_lt(v_x_614_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__9(v_vs_652_, v_v_613_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_659_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_children_653_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v_k_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_c_666_; lean_object* v___x_668_; 
v_k_663_ = lean_array_fget_borrowed(v_keys_612_, v_x_614_);
v___x_664_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___closed__1));
lean_inc_n(v_k_663_, 2);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_k_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v_c_666_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10(v_x_614_, v_keys_612_, v_v_613_, v_k_663_, v_children_653_, v___x_665_);
lean_dec_ref_known(v___x_665_, 2);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v_c_666_);
v___x_668_ = v___x_655_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_vs_652_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_c_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__2(lean_object* v_x_671_, lean_object* v_keys_672_, lean_object* v_v_673_, lean_object* v_k_674_, lean_object* v_x_675_){
_start:
{
lean_object* v_snd_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_686_; 
v_snd_676_ = lean_ctor_get(v_x_675_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_x_675_, 0);
lean_dec(v_unused_687_);
v___x_678_ = v_x_675_;
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snd_676_);
lean_dec(v_x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_686_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_c_682_; lean_object* v___x_684_; 
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_x_671_, v___x_680_);
v_c_682_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_672_, v_v_673_, v___x_681_, v_snd_676_);
lean_dec(v___x_681_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v_c_682_);
lean_ctor_set(v___x_678_, 0, v_k_674_);
v___x_684_ = v___x_678_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_k_674_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_c_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__2___boxed(lean_object* v_x_688_, lean_object* v_keys_689_, lean_object* v_v_690_, lean_object* v_k_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___lam__2(v_x_688_, v_keys_689_, v_v_690_, v_k_691_, v_x_692_);
lean_dec_ref(v_keys_689_);
lean_dec(v_x_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___redArg___boxed(lean_object* v_x_694_, lean_object* v_keys_695_, lean_object* v_v_696_, lean_object* v_k_697_, lean_object* v_as_698_, lean_object* v_k_699_, lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___redArg(v_x_694_, v_keys_695_, v_v_696_, v_k_697_, v_as_698_, v_k_699_, v_x_700_, v_x_701_);
lean_dec_ref(v_k_699_);
lean_dec_ref(v_keys_695_);
lean_dec(v_x_694_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object* v_keys_703_, lean_object* v_v_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_703_, v_v_704_, v_x_705_, v_x_706_);
lean_dec(v_x_705_);
lean_dec_ref(v_keys_703_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10___boxed(lean_object* v_x_708_, lean_object* v_keys_709_, lean_object* v_v_710_, lean_object* v_k_711_, lean_object* v_as_712_, lean_object* v_k_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10(v_x_708_, v_keys_709_, v_v_710_, v_k_711_, v_as_712_, v_k_713_);
lean_dec_ref(v_k_713_);
lean_dec_ref(v_keys_709_);
lean_dec(v_x_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(lean_object* v_keys_715_, lean_object* v_v_716_, lean_object* v_x_717_){
_start:
{
if (lean_obj_tag(v_x_717_) == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_715_, v_v_716_, v___x_718_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
else
{
lean_object* v_val_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_730_; 
v_val_721_ = lean_ctor_get(v_x_717_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_717_);
if (v_isSharedCheck_730_ == 0)
{
v___x_723_ = v_x_717_;
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_val_721_);
lean_dec(v_x_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_keys_715_, v_v_716_, v___x_725_, v_val_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_726_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0___boxed(lean_object* v_keys_731_, lean_object* v_v_732_, lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_731_, v_v_732_, v_x_733_);
lean_dec_ref(v_keys_731_);
return v_res_734_;
}
}
lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object* v_keys_735_, lean_object* v_v_736_, lean_object* v_x_737_, size_t v_x_738_, size_t v_x_739_, lean_object* v_x_740_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
lean_object* v_es_741_; size_t v___x_742_; size_t v___x_743_; lean_object* v_j_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_es_741_ = lean_ctor_get(v_x_737_, 0);
v___x_742_ = ((size_t)31ULL);
v___x_743_ = lean_usize_land(v_x_738_, v___x_742_);
v_j_744_ = lean_usize_to_nat(v___x_743_);
v___x_745_ = lean_array_get_size(v_es_741_);
v___x_746_ = lean_nat_dec_lt(v_j_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_dec(v_j_744_);
lean_dec(v_x_740_);
lean_dec_ref(v_v_736_);
return v_x_737_;
}
else
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_814_; 
lean_inc_ref(v_es_741_);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_x_737_, 0);
lean_dec(v_unused_815_);
v___x_748_ = v_x_737_;
v_isShared_749_ = v_isSharedCheck_814_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_x_737_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_814_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_v_750_; lean_object* v___x_751_; lean_object* v_xs_x27_752_; lean_object* v___y_754_; 
v_v_750_ = lean_array_fget(v_es_741_, v_j_744_);
v___x_751_ = lean_box(0);
v_xs_x27_752_ = lean_array_fset(v_es_741_, v_j_744_, v___x_751_);
switch(lean_obj_tag(v_v_750_))
{
case 0:
{
lean_object* v_key_759_; lean_object* v_val_760_; uint8_t v___x_761_; 
v_key_759_ = lean_ctor_get(v_v_750_, 0);
v_val_760_ = lean_ctor_get(v_v_750_, 1);
v___x_761_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_740_, v_key_759_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_box(0);
v___x_763_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_735_, v_v_736_, v___x_762_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_dec(v_x_740_);
v___y_754_ = v_v_750_;
goto v___jp_753_;
}
else
{
lean_object* v_val_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_772_; 
lean_inc(v_val_760_);
lean_inc(v_key_759_);
lean_dec_ref_known(v_v_750_, 2);
v_val_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_772_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_val_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_772_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_759_, v_val_760_, v_x_740_, v_val_764_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v___y_754_ = v___x_770_;
goto v___jp_753_;
}
}
}
}
else
{
lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
lean_inc(v_val_760_);
v_isSharedCheck_783_ = !lean_is_exclusive(v_v_750_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_784_ = lean_ctor_get(v_v_750_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_v_750_, 0);
lean_dec(v_unused_785_);
v___x_774_ = v_v_750_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_dec(v_v_750_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_val_760_);
v___x_777_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_735_, v_v_736_, v___x_776_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v___x_778_; 
lean_del_object(v___x_774_);
lean_dec(v_x_740_);
v___x_778_ = lean_box(2);
v___y_754_ = v___x_778_;
goto v___jp_753_;
}
else
{
lean_object* v_val_779_; lean_object* v___x_781_; 
v_val_779_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_779_);
lean_dec_ref_known(v___x_777_, 1);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_val_779_);
lean_ctor_set(v___x_774_, 0, v_x_740_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_x_740_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_val_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v___y_754_ = v___x_781_;
goto v___jp_753_;
}
}
}
}
}
case 1:
{
lean_object* v_node_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_809_; 
v_node_786_ = lean_ctor_get(v_v_750_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v_v_750_);
if (v_isSharedCheck_809_ == 0)
{
v___x_788_ = v_v_750_;
v_isShared_789_ = v_isSharedCheck_809_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_node_786_);
lean_dec(v_v_750_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_809_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_newNode_794_; lean_object* v___x_795_; 
v___x_790_ = ((size_t)5ULL);
v___x_791_ = lean_usize_shift_right(v_x_738_, v___x_790_);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_add(v_x_739_, v___x_792_);
v_newNode_794_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_735_, v_v_736_, v_node_786_, v___x_791_, v___x_793_, v_x_740_);
lean_inc_ref(v_newNode_794_);
v___x_795_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_797_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_newNode_794_);
v___x_797_ = v___x_788_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_newNode_794_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
v___y_754_ = v___x_797_;
goto v___jp_753_;
}
}
else
{
lean_object* v_val_799_; lean_object* v_fst_800_; lean_object* v_snd_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_newNode_794_);
lean_del_object(v___x_788_);
v_val_799_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_795_, 1);
v_fst_800_ = lean_ctor_get(v_val_799_, 0);
v_snd_801_ = lean_ctor_get(v_val_799_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_val_799_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v_val_799_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_snd_801_);
lean_inc(v_fst_800_);
lean_dec(v_val_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_fst_800_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_754_ = v___x_806_;
goto v___jp_753_;
}
}
}
}
}
default: 
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_box(0);
v___x_811_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_735_, v_v_736_, v___x_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_dec(v_x_740_);
v___y_754_ = v_v_750_;
goto v___jp_753_;
}
else
{
lean_object* v_val_812_; lean_object* v___x_813_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_x_740_);
lean_ctor_set(v___x_813_, 1, v_val_812_);
v___y_754_ = v___x_813_;
goto v___jp_753_;
}
}
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_array_fset(v_xs_x27_752_, v_j_744_, v___y_754_);
lean_dec(v_j_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_755_);
v___x_757_ = v___x_748_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v_ks_816_; lean_object* v_vs_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_850_; 
v_ks_816_ = lean_ctor_get(v_x_737_, 0);
v_vs_817_ = lean_ctor_get(v_x_737_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_850_ == 0)
{
v___x_819_ = v_x_737_;
v_isShared_820_ = v_isSharedCheck_850_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_vs_817_);
lean_inc(v_ks_816_);
lean_dec(v_x_737_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_850_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; 
v___x_821_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__12(v_ks_816_, v_x_740_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_823_; 
if (v_isShared_820_ == 0)
{
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_ks_816_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_vs_817_);
v___x_823_ = v_reuseFailAlloc_828_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_box(0);
v___x_825_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_735_, v_v_736_, v___x_824_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_dec(v_x_740_);
return v___x_823_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; 
v_val_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(v___x_823_, v_x_738_, v_x_739_, v_x_740_, v_val_826_);
return v___x_827_;
}
}
}
else
{
lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_849_; 
v_val_829_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_849_ == 0)
{
v___x_831_ = v___x_821_;
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_dec(v___x_821_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_v_x27_833_; lean_object* v_keys_834_; lean_object* v_vals_835_; lean_object* v___x_837_; 
v_v_x27_833_ = lean_array_fget(v_vs_817_, v_val_829_);
lean_inc(v_val_829_);
v_keys_834_ = l_Array_eraseIdx___redArg(v_ks_816_, v_val_829_);
v_vals_835_ = l_Array_eraseIdx___redArg(v_vs_817_, v_val_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_v_x27_833_);
v___x_837_ = v___x_831_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_v_x27_833_);
v___x_837_ = v_reuseFailAlloc_848_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___lam__0(v_keys_735_, v_v_736_, v___x_837_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_840_; 
lean_dec(v_x_740_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_vals_835_);
lean_ctor_set(v___x_819_, 0, v_keys_834_);
v___x_840_ = v___x_819_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_keys_834_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_vals_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v_val_842_; lean_object* v_keys_843_; lean_object* v_vals_844_; lean_object* v___x_846_; 
v_val_842_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_842_);
lean_dec_ref_known(v___x_838_, 1);
v_keys_843_ = lean_array_push(v_keys_834_, v_x_740_);
v_vals_844_ = lean_array_push(v_vals_835_, v_val_842_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_vals_844_);
lean_ctor_set(v___x_819_, 0, v_keys_843_);
v___x_846_ = v___x_819_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_keys_843_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_vals_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_735_ = stack[0].m_obj;
lean_object* v_v_736_ = stack[1].m_obj;
lean_object* v_x_737_ = stack[2].m_obj;
size_t v_x_738_ = stack[3].m_num;
size_t v_x_739_ = stack[4].m_num;
lean_object* v_x_740_ = stack[5].m_obj;
lean_object* v_res_851_;
v_res_851_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_735_, v_v_736_, v_x_737_, v_x_738_, v_x_739_, v_x_740_);
stack->m_obj
 = v_res_851_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___boxed(lean_object* v_keys_852_, lean_object* v_v_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
size_t v_x_4057__boxed_858_; size_t v_x_4058__boxed_859_; lean_object* v_res_860_; 
v_x_4057__boxed_858_ = lean_unbox_usize(v_x_855_);
lean_dec(v_x_855_);
v_x_4058__boxed_859_ = lean_unbox_usize(v_x_856_);
lean_dec(v_x_856_);
v_res_860_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_852_, v_v_853_, v_x_854_, v_x_4057__boxed_858_, v_x_4058__boxed_859_, v_x_857_);
lean_dec_ref(v_keys_852_);
return v_res_860_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Meta_DiscrTree_instInhabited___redArg();
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object* v_msg_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0);
v___x_864_ = lean_panic_fn_borrowed(v___x_863_, v_msg_862_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_868_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2));
v___x_869_ = lean_unsigned_to_nat(23u);
v___x_870_ = lean_unsigned_to_nat(177u);
v___x_871_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1));
v___x_872_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0));
v___x_873_ = l_mkPanicMessageWithDecl(v___x_872_, v___x_871_, v___x_870_, v___x_869_, v___x_868_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object* v_d_874_, lean_object* v_keys_875_, lean_object* v_v_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_array_get_size(v_keys_875_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_nat_dec_eq(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v_k_881_; uint64_t v___x_882_; size_t v_h_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_880_ = lean_box(0);
v_k_881_ = lean_array_get_borrowed(v___x_880_, v_keys_875_, v___x_878_);
v___x_882_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_881_);
v_h_883_ = lean_uint64_to_usize(v___x_882_);
v___x_884_ = ((size_t)1ULL);
lean_inc(v_k_881_);
v___x_885_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(v_keys_875_, v_v_876_, v_d_874_, v_h_883_, v___x_884_, v_k_881_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v_v_876_);
lean_dec_ref(v_d_874_);
v___x_886_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3);
v___x_887_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v___x_886_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object* v_d_888_, lean_object* v_keys_889_, lean_object* v_v_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_d_888_, v_keys_889_, v_v_890_);
lean_dec_ref(v_keys_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
lean_object* v_ks_896_; lean_object* v_vs_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_921_; 
v_ks_896_ = lean_ctor_get(v_x_892_, 0);
v_vs_897_ = lean_ctor_get(v_x_892_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_892_);
if (v_isSharedCheck_921_ == 0)
{
v___x_899_ = v_x_892_;
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_vs_897_);
lean_inc(v_ks_896_);
lean_dec(v_x_892_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_array_get_size(v_ks_896_);
v___x_902_ = lean_nat_dec_lt(v_x_893_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_dec(v_x_893_);
v___x_903_ = lean_array_push(v_ks_896_, v_x_894_);
v___x_904_ = lean_array_push(v_vs_897_, v_x_895_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_904_);
lean_ctor_set(v___x_899_, 0, v___x_903_);
v___x_906_ = v___x_899_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_object* v_k_x27_908_; uint8_t v___x_909_; 
v_k_x27_908_ = lean_array_fget_borrowed(v_ks_896_, v_x_893_);
v___x_909_ = lean_name_eq(v_x_894_, v_k_x27_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_911_; 
if (v_isShared_900_ == 0)
{
v___x_911_ = v___x_899_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_ks_896_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_vs_897_);
v___x_911_ = v_reuseFailAlloc_915_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_unsigned_to_nat(1u);
v___x_913_ = lean_nat_add(v_x_893_, v___x_912_);
lean_dec(v_x_893_);
v_x_892_ = v___x_911_;
v_x_893_ = v___x_913_;
goto _start;
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = lean_array_fset(v_ks_896_, v_x_893_, v_x_894_);
v___x_917_ = lean_array_fset(v_vs_897_, v_x_893_, v_x_895_);
lean_dec(v_x_893_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_917_);
lean_ctor_set(v___x_899_, 0, v___x_916_);
v___x_919_ = v___x_899_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_922_, lean_object* v_k_923_, lean_object* v_v_924_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_n_922_, v___x_925_, v_k_923_, v_v_924_);
return v___x_926_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object* v_x_927_, size_t v_x_928_, size_t v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v_es_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v_j_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_es_932_ = lean_ctor_get(v_x_927_, 0);
v___x_933_ = ((size_t)31ULL);
v___x_934_ = lean_usize_land(v_x_928_, v___x_933_);
v_j_935_ = lean_usize_to_nat(v___x_934_);
v___x_936_ = lean_array_get_size(v_es_932_);
v___x_937_ = lean_nat_dec_lt(v_j_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec(v_j_935_);
lean_dec(v_x_931_);
lean_dec(v_x_930_);
return v_x_927_;
}
else
{
lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_976_; 
lean_inc_ref(v_es_932_);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_x_927_, 0);
lean_dec(v_unused_977_);
v___x_939_ = v_x_927_;
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
else
{
lean_dec(v_x_927_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_976_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_v_941_; lean_object* v___x_942_; lean_object* v_xs_x27_943_; lean_object* v___y_945_; 
v_v_941_ = lean_array_fget(v_es_932_, v_j_935_);
v___x_942_ = lean_box(0);
v_xs_x27_943_ = lean_array_fset(v_es_932_, v_j_935_, v___x_942_);
switch(lean_obj_tag(v_v_941_))
{
case 0:
{
lean_object* v_key_950_; lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_961_; 
v_key_950_ = lean_ctor_get(v_v_941_, 0);
v_val_951_ = lean_ctor_get(v_v_941_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_v_941_);
if (v_isSharedCheck_961_ == 0)
{
v___x_953_ = v_v_941_;
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_inc(v_key_950_);
lean_dec(v_v_941_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = lean_name_eq(v_x_930_, v_key_950_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_del_object(v___x_953_);
v___x_956_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_950_, v_val_951_, v_x_930_, v_x_931_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___y_945_ = v___x_957_;
goto v___jp_944_;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_val_951_);
lean_dec(v_key_950_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_x_931_);
lean_ctor_set(v___x_953_, 0, v_x_930_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_x_930_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_x_931_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v___y_945_ = v___x_959_;
goto v___jp_944_;
}
}
}
}
case 1:
{
lean_object* v_node_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_974_; 
v_node_962_ = lean_ctor_get(v_v_941_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_v_941_);
if (v_isSharedCheck_974_ == 0)
{
v___x_964_ = v_v_941_;
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_node_962_);
lean_dec(v_v_941_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
size_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_966_ = ((size_t)5ULL);
v___x_967_ = lean_usize_shift_right(v_x_928_, v___x_966_);
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_add(v_x_929_, v___x_968_);
v___x_970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_node_962_, v___x_967_, v___x_969_, v_x_930_, v_x_931_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_970_);
v___x_972_ = v___x_964_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v___y_945_ = v___x_972_;
goto v___jp_944_;
}
}
}
default: 
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_x_930_);
lean_ctor_set(v___x_975_, 1, v_x_931_);
v___y_945_ = v___x_975_;
goto v___jp_944_;
}
}
v___jp_944_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = lean_array_fset(v_xs_x27_943_, v_j_935_, v___y_945_);
lean_dec(v_j_935_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_946_);
v___x_948_ = v___x_939_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v_ks_978_; lean_object* v_vs_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_997_; 
v_ks_978_ = lean_ctor_get(v_x_927_, 0);
v_vs_979_ = lean_ctor_get(v_x_927_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_997_ == 0)
{
v___x_981_ = v_x_927_;
v_isShared_982_ = v_isSharedCheck_997_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_vs_979_);
lean_inc(v_ks_978_);
lean_dec(v_x_927_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_997_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_ks_978_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_vs_979_);
v___x_984_ = v_reuseFailAlloc_996_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v_newNode_985_; size_t v___x_986_; uint8_t v___x_987_; 
v_newNode_985_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v___x_984_, v_x_930_, v_x_931_);
v___x_986_ = ((size_t)7ULL);
v___x_987_ = lean_usize_dec_le(v___x_986_, v_x_929_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_985_);
v___x_989_ = lean_unsigned_to_nat(4u);
v___x_990_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
lean_dec(v___x_988_);
if (v___x_990_ == 0)
{
lean_object* v_ks_991_; lean_object* v_vs_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_ks_991_ = lean_ctor_get(v_newNode_985_, 0);
lean_inc_ref(v_ks_991_);
v_vs_992_ = lean_ctor_get(v_newNode_985_, 1);
lean_inc_ref(v_vs_992_);
lean_dec_ref(v_newNode_985_);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg___closed__0);
v___x_995_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_x_929_, v_ks_991_, v_vs_992_, v___x_993_, v___x_994_);
lean_dec_ref(v_vs_992_);
lean_dec_ref(v_ks_991_);
return v___x_995_;
}
else
{
return v_newNode_985_;
}
}
else
{
return v_newNode_985_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_927_ = stack[0].m_obj;
size_t v_x_928_ = stack[1].m_num;
size_t v_x_929_ = stack[2].m_num;
lean_object* v_x_930_ = stack[3].m_obj;
lean_object* v_x_931_ = stack[4].m_obj;
lean_object* v_res_998_;
v_res_998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_927_, v_x_928_, v_x_929_, v_x_930_, v_x_931_);
stack->m_obj
 = v_res_998_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_999_, lean_object* v_keys_1000_, lean_object* v_vals_1001_, lean_object* v_i_1002_, lean_object* v_entries_1003_){
_start:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_array_get_size(v_keys_1000_);
v___x_1005_ = lean_nat_dec_lt(v_i_1002_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_dec(v_i_1002_);
return v_entries_1003_;
}
else
{
lean_object* v_k_1006_; lean_object* v_v_1007_; uint64_t v___y_1009_; 
v_k_1006_ = lean_array_fget_borrowed(v_keys_1000_, v_i_1002_);
v_v_1007_ = lean_array_fget_borrowed(v_vals_1001_, v_i_1002_);
if (lean_obj_tag(v_k_1006_) == 0)
{
uint64_t v___x_1020_; 
v___x_1020_ = 1723ULL;
v___y_1009_ = v___x_1020_;
goto v___jp_1008_;
}
else
{
uint64_t v_hash_1021_; 
v_hash_1021_ = lean_ctor_get_uint64(v_k_1006_, sizeof(void*)*2);
v___y_1009_ = v_hash_1021_;
goto v___jp_1008_;
}
v___jp_1008_:
{
size_t v_h_1010_; size_t v___x_1011_; lean_object* v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; size_t v_h_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_h_1010_ = lean_uint64_to_usize(v___y_1009_);
v___x_1011_ = ((size_t)5ULL);
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = ((size_t)1ULL);
v___x_1014_ = lean_usize_sub(v_depth_999_, v___x_1013_);
v___x_1015_ = lean_usize_mul(v___x_1011_, v___x_1014_);
v_h_1016_ = lean_usize_shift_right(v_h_1010_, v___x_1015_);
v___x_1017_ = lean_nat_add(v_i_1002_, v___x_1012_);
lean_dec(v_i_1002_);
lean_inc(v_v_1007_);
lean_inc(v_k_1006_);
v___x_1018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_entries_1003_, v_h_1016_, v_depth_999_, v_k_1006_, v_v_1007_);
v_i_1002_ = v___x_1017_;
v_entries_1003_ = v___x_1018_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_999_ = stack[0].m_num;
lean_object* v_keys_1000_ = stack[1].m_obj;
lean_object* v_vals_1001_ = stack[2].m_obj;
lean_object* v_i_1002_ = stack[3].m_obj;
lean_object* v_entries_1003_ = stack[4].m_obj;
lean_object* v_res_1022_;
v_res_1022_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_999_, v_keys_1000_, v_vals_1001_, v_i_1002_, v_entries_1003_);
stack->m_obj
 = v_res_1022_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1023_, lean_object* v_keys_1024_, lean_object* v_vals_1025_, lean_object* v_i_1026_, lean_object* v_entries_1027_){
_start:
{
size_t v_depth_boxed_1028_; lean_object* v_res_1029_; 
v_depth_boxed_1028_ = lean_unbox_usize(v_depth_1023_);
lean_dec(v_depth_1023_);
v_res_1029_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1028_, v_keys_1024_, v_vals_1025_, v_i_1026_, v_entries_1027_);
lean_dec_ref(v_vals_1025_);
lean_dec_ref(v_keys_1024_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
size_t v_x_4561__boxed_1035_; size_t v_x_4562__boxed_1036_; lean_object* v_res_1037_; 
v_x_4561__boxed_1035_ = lean_unbox_usize(v_x_1031_);
lean_dec(v_x_1031_);
v_x_4562__boxed_1036_ = lean_unbox_usize(v_x_1032_);
lean_dec(v_x_1032_);
v_res_1037_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1030_, v_x_4561__boxed_1035_, v_x_4562__boxed_1036_, v_x_1033_, v_x_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
uint64_t v___y_1042_; 
if (lean_obj_tag(v_x_1039_) == 0)
{
uint64_t v___x_1046_; 
v___x_1046_ = 1723ULL;
v___y_1042_ = v___x_1046_;
goto v___jp_1041_;
}
else
{
uint64_t v_hash_1047_; 
v_hash_1047_ = lean_ctor_get_uint64(v_x_1039_, sizeof(void*)*2);
v___y_1042_ = v_hash_1047_;
goto v___jp_1041_;
}
v___jp_1041_:
{
size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_uint64_to_usize(v___y_1042_);
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1038_, v___x_1043_, v___x_1044_, v_x_1039_, v_x_1040_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object* v_xs_1048_, lean_object* v_v_1049_, lean_object* v_i_1050_){
_start:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = lean_array_get_size(v_xs_1048_);
v___x_1052_ = lean_nat_dec_lt(v_i_1050_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec(v_i_1050_);
v___x_1053_ = lean_box(0);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_array_fget_borrowed(v_xs_1048_, v_i_1050_);
v___x_1055_ = lean_name_eq(v___x_1054_, v_v_1049_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(1u);
v___x_1057_ = lean_nat_add(v_i_1050_, v___x_1056_);
lean_dec(v_i_1050_);
v_i_1050_ = v___x_1057_;
goto _start;
}
else
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_i_1050_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_xs_1060_, lean_object* v_v_1061_, lean_object* v_i_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_1060_, v_v_1061_, v_i_1062_);
lean_dec(v_v_1061_);
lean_dec_ref(v_xs_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object* v_xs_1064_, lean_object* v_v_1065_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_1064_, v_v_1065_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object* v_xs_1068_, lean_object* v_v_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_xs_1068_, v_v_1069_);
lean_dec(v_v_1069_);
lean_dec_ref(v_xs_1068_);
return v_res_1070_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object* v_x_1071_, size_t v_x_1072_, lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v_es_1074_; lean_object* v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; lean_object* v_j_1078_; lean_object* v_entry_1079_; 
v_es_1074_ = lean_ctor_get(v_x_1071_, 0);
v___x_1075_ = lean_box(2);
v___x_1076_ = ((size_t)31ULL);
v___x_1077_ = lean_usize_land(v_x_1072_, v___x_1076_);
v_j_1078_ = lean_usize_to_nat(v___x_1077_);
v_entry_1079_ = lean_array_get(v___x_1075_, v_es_1074_, v_j_1078_);
switch(lean_obj_tag(v_entry_1079_))
{
case 0:
{
lean_object* v_key_1080_; uint8_t v___x_1081_; 
v_key_1080_ = lean_ctor_get(v_entry_1079_, 0);
lean_inc(v_key_1080_);
lean_dec_ref_known(v_entry_1079_, 2);
v___x_1081_ = lean_name_eq(v_x_1073_, v_key_1080_);
lean_dec(v_key_1080_);
if (v___x_1081_ == 0)
{
lean_dec(v_j_1078_);
return v_x_1071_;
}
else
{
lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
lean_inc_ref(v_es_1074_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_x_1071_, 0);
lean_dec(v_unused_1090_);
v___x_1083_ = v_x_1071_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_dec(v_x_1071_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_array_set(v_es_1074_, v_j_1078_, v___x_1075_);
lean_dec(v_j_1078_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
case 1:
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1125_; 
lean_inc_ref(v_es_1074_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_x_1071_, 0);
lean_dec(v_unused_1126_);
v___x_1092_ = v_x_1071_;
v_isShared_1093_ = v_isSharedCheck_1125_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_x_1071_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1125_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_node_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1124_; 
v_node_1094_ = lean_ctor_get(v_entry_1079_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_entry_1079_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1096_ = v_entry_1079_;
v_isShared_1097_ = v_isSharedCheck_1124_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_node_1094_);
lean_dec(v_entry_1079_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1124_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
size_t v___x_1098_; lean_object* v_entries_1099_; size_t v___x_1100_; lean_object* v_newNode_1101_; lean_object* v___x_1102_; 
v___x_1098_ = ((size_t)5ULL);
v_entries_1099_ = lean_array_set(v_es_1074_, v_j_1078_, v___x_1075_);
v___x_1100_ = lean_usize_shift_right(v_x_1072_, v___x_1098_);
v_newNode_1101_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_node_1094_, v___x_1100_, v_x_1073_);
lean_inc_ref(v_newNode_1101_);
v___x_1102_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1101_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1104_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v_newNode_1101_);
v___x_1104_ = v___x_1096_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_newNode_1101_);
v___x_1104_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_array_set(v_entries_1099_, v_j_1078_, v___x_1104_);
lean_dec(v_j_1078_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1105_);
v___x_1107_ = v___x_1092_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
else
{
lean_object* v_val_1110_; lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_newNode_1101_);
lean_del_object(v___x_1096_);
v_val_1110_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v___x_1102_, 1);
v_fst_1111_ = lean_ctor_get(v_val_1110_, 0);
v_snd_1112_ = lean_ctor_get(v_val_1110_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_val_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1114_ = v_val_1110_;
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v_val_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1123_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_snd_1112_);
v___x_1117_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_array_set(v_entries_1099_, v_j_1078_, v___x_1117_);
lean_dec(v_j_1078_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1118_);
v___x_1120_ = v___x_1092_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1078_);
return v_x_1071_;
}
}
}
else
{
lean_object* v_ks_1127_; lean_object* v_vs_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1142_; 
v_ks_1127_ = lean_ctor_get(v_x_1071_, 0);
v_vs_1128_ = lean_ctor_get(v_x_1071_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1130_ = v_x_1071_;
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_vs_1128_);
lean_inc(v_ks_1127_);
lean_dec(v_x_1071_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1142_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_ks_1127_, v_x_1073_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1134_; 
if (v_isShared_1131_ == 0)
{
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_ks_1127_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_vs_1128_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_object* v_val_1136_; lean_object* v_keys_x27_1137_; lean_object* v_vals_x27_1138_; lean_object* v___x_1140_; 
v_val_1136_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_n(v_val_1136_, 2);
lean_dec_ref_known(v___x_1132_, 1);
v_keys_x27_1137_ = l_Array_eraseIdx___redArg(v_ks_1127_, v_val_1136_);
v_vals_x27_1138_ = l_Array_eraseIdx___redArg(v_vs_1128_, v_val_1136_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v_vals_x27_1138_);
lean_ctor_set(v___x_1130_, 0, v_keys_x27_1137_);
v___x_1140_ = v___x_1130_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_keys_x27_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_vals_x27_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1071_ = stack[0].m_obj;
size_t v_x_1072_ = stack[1].m_num;
lean_object* v_x_1073_ = stack[2].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1071_, v_x_1072_, v_x_1073_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
size_t v_x_4859__boxed_1147_; lean_object* v_res_1148_; 
v_x_4859__boxed_1147_ = lean_unbox_usize(v_x_1145_);
lean_dec(v_x_1145_);
v_res_1148_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1144_, v_x_4859__boxed_1147_, v_x_1146_);
lean_dec(v_x_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
uint64_t v___y_1152_; 
if (lean_obj_tag(v_x_1150_) == 0)
{
uint64_t v___x_1155_; 
v___x_1155_ = 1723ULL;
v___y_1152_ = v___x_1155_;
goto v___jp_1151_;
}
else
{
uint64_t v_hash_1156_; 
v_hash_1156_ = lean_ctor_get_uint64(v_x_1150_, sizeof(void*)*2);
v___y_1152_ = v_hash_1156_;
goto v___jp_1151_;
}
v___jp_1151_:
{
size_t v_h_1153_; lean_object* v___x_1154_; 
v_h_1153_ = lean_uint64_to_usize(v___y_1152_);
v___x_1154_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1149_, v_h_1153_, v_x_1150_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1157_, v_x_1158_);
lean_dec(v_x_1158_);
return v_res_1159_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object* v_s_1160_, lean_object* v_keys_1161_, lean_object* v_declName_1162_, uint8_t v_phase_1163_, lean_object* v_proc_1164_){
_start:
{
lean_object* v_pre_1165_; lean_object* v_eval_1166_; lean_object* v_post_1167_; lean_object* v_simprocNames_1168_; lean_object* v_erased_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1190_; 
v_pre_1165_ = lean_ctor_get(v_s_1160_, 0);
v_eval_1166_ = lean_ctor_get(v_s_1160_, 1);
v_post_1167_ = lean_ctor_get(v_s_1160_, 2);
v_simprocNames_1168_ = lean_ctor_get(v_s_1160_, 3);
v_erased_1169_ = lean_ctor_get(v_s_1160_, 4);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_s_1160_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1171_ = v_s_1160_;
v_isShared_1172_ = v_isSharedCheck_1190_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_erased_1169_);
lean_inc(v_simprocNames_1168_);
lean_inc(v_post_1167_);
lean_inc(v_eval_1166_);
lean_inc(v_pre_1165_);
lean_dec(v_s_1160_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1190_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v_entry_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_inc_ref(v_keys_1161_);
lean_inc_n(v_declName_1162_, 2);
v___x_1173_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1173_, 0, v_declName_1162_);
lean_ctor_set(v___x_1173_, 1, v_keys_1161_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*2, v_phase_1163_);
v_entry_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_entry_1174_, 0, v___x_1173_);
lean_ctor_set(v_entry_1174_, 1, v_proc_1164_);
v___x_1175_ = lean_box(0);
v___x_1176_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_simprocNames_1168_, v_declName_1162_, v___x_1175_);
v___x_1177_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_erased_1169_, v_declName_1162_);
lean_dec(v_declName_1162_);
switch(v_phase_1163_)
{
case 0:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_pre_1165_, v_keys_1161_, v_entry_1174_);
lean_dec_ref(v_keys_1161_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 4, v___x_1177_);
lean_ctor_set(v___x_1171_, 3, v___x_1176_);
lean_ctor_set(v___x_1171_, 0, v___x_1178_);
v___x_1180_ = v___x_1171_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_eval_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_post_1167_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v___x_1177_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
case 1:
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_eval_1166_, v_keys_1161_, v_entry_1174_);
lean_dec_ref(v_keys_1161_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 4, v___x_1177_);
lean_ctor_set(v___x_1171_, 3, v___x_1176_);
lean_ctor_set(v___x_1171_, 1, v___x_1182_);
v___x_1184_ = v___x_1171_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_pre_1165_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_post_1167_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v___x_1177_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
default: 
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_post_1167_, v_keys_1161_, v_entry_1174_);
lean_dec_ref(v_keys_1161_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 4, v___x_1177_);
lean_ctor_set(v___x_1171_, 3, v___x_1176_);
lean_ctor_set(v___x_1171_, 2, v___x_1186_);
v___x_1188_ = v___x_1171_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_pre_1165_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_eval_1166_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v___x_1177_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1160_ = stack[0].m_obj;
lean_object* v_keys_1161_ = stack[1].m_obj;
lean_object* v_declName_1162_ = stack[2].m_obj;
uint8_t v_phase_1163_ = stack[3].m_num;
lean_object* v_proc_1164_ = stack[4].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_1160_, v_keys_1161_, v_declName_1162_, v_phase_1163_, v_proc_1164_);
stack->m_obj
 = v_res_1191_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object* v_s_1192_, lean_object* v_keys_1193_, lean_object* v_declName_1194_, lean_object* v_phase_1195_, lean_object* v_proc_1196_){
_start:
{
uint8_t v_phase_boxed_1197_; lean_object* v_res_1198_; 
v_phase_boxed_1197_ = lean_unbox(v_phase_1195_);
v_res_1198_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_1192_, v_keys_1193_, v_declName_1194_, v_phase_boxed_1197_, v_proc_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object* v_00_u03b2_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_x_1200_, v_x_1201_, v_x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object* v_00_u03b2_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1205_, v_x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object* v_00_u03b2_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(v_00_u03b2_1208_, v_x_1209_, v_x_1210_);
lean_dec(v_x_1210_);
return v_res_1211_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object* v_00_u03b2_1212_, lean_object* v_x_1213_, size_t v_x_1214_, size_t v_x_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1213_, v_x_1214_, v_x_1215_, v_x_1216_, v_x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1213_ = stack[1].m_obj;
size_t v_x_1214_ = stack[2].m_num;
size_t v_x_1215_ = stack[3].m_num;
lean_object* v_x_1216_ = stack[4].m_obj;
lean_object* v_x_1217_ = stack[5].m_obj;
lean_object* v_res_1219_;
v_res_1219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_box(0), v_x_1213_, v_x_1214_, v_x_1215_, v_x_1216_, v_x_1217_);
stack->m_obj
 = v_res_1219_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_, lean_object* v_x_1225_){
_start:
{
size_t v_x_5171__boxed_1226_; size_t v_x_5172__boxed_1227_; lean_object* v_res_1228_; 
v_x_5171__boxed_1226_ = lean_unbox_usize(v_x_1222_);
lean_dec(v_x_1222_);
v_x_5172__boxed_1227_ = lean_unbox_usize(v_x_1223_);
lean_dec(v_x_1223_);
v_res_1228_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(v_00_u03b2_1220_, v_x_1221_, v_x_5171__boxed_1226_, v_x_5172__boxed_1227_, v_x_1224_, v_x_1225_);
return v_res_1228_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object* v_00_u03b2_1229_, lean_object* v_x_1230_, size_t v_x_1231_, lean_object* v_x_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1230_, v_x_1231_, v_x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1230_ = stack[1].m_obj;
size_t v_x_1231_ = stack[2].m_num;
lean_object* v_x_1232_ = stack[3].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_box(0), v_x_1230_, v_x_1231_, v_x_1232_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
size_t v_x_5199__boxed_1239_; lean_object* v_res_1240_; 
v_x_5199__boxed_1239_ = lean_unbox_usize(v_x_1237_);
lean_dec(v_x_1237_);
v_res_1240_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(v_00_u03b2_1235_, v_x_1236_, v_x_5199__boxed_1239_, v_x_1238_);
lean_dec(v_x_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1241_, lean_object* v_n_1242_, lean_object* v_k_1243_, lean_object* v_v_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v_n_1242_, v_k_1243_, v_v_1244_);
return v___x_1245_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1246_, size_t v_depth_1247_, lean_object* v_keys_1248_, lean_object* v_vals_1249_, lean_object* v_heq_1250_, lean_object* v_i_1251_, lean_object* v_entries_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_1247_, v_keys_1248_, v_vals_1249_, v_i_1251_, v_entries_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1247_ = stack[1].m_num;
lean_object* v_keys_1248_ = stack[2].m_obj;
lean_object* v_vals_1249_ = stack[3].m_obj;
lean_object* v_i_1251_ = stack[5].m_obj;
lean_object* v_entries_1252_ = stack[6].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_box(0), v_depth_1247_, v_keys_1248_, v_vals_1249_, lean_box(0), v_i_1251_, v_entries_1252_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1255_, lean_object* v_depth_1256_, lean_object* v_keys_1257_, lean_object* v_vals_1258_, lean_object* v_heq_1259_, lean_object* v_i_1260_, lean_object* v_entries_1261_){
_start:
{
size_t v_depth_boxed_1262_; lean_object* v_res_1263_; 
v_depth_boxed_1262_ = lean_unbox_usize(v_depth_1256_);
lean_dec(v_depth_1256_);
v_res_1263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(v_00_u03b2_1255_, v_depth_boxed_1262_, v_keys_1257_, v_vals_1258_, v_heq_1259_, v_i_1260_, v_entries_1261_);
lean_dec_ref(v_vals_1258_);
lean_dec_ref(v_keys_1257_);
return v_res_1263_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, size_t v_x_1266_, size_t v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___redArg(v_x_1265_, v_x_1266_, v_x_1267_, v_x_1268_, v_x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1265_ = stack[1].m_obj;
size_t v_x_1266_ = stack[2].m_num;
size_t v_x_1267_ = stack[3].m_num;
lean_object* v_x_1268_ = stack[4].m_obj;
lean_object* v_x_1269_ = stack[5].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13(lean_box(0), v_x_1265_, v_x_1266_, v_x_1267_, v_x_1268_, v_x_1269_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13___boxed(lean_object* v_00_u03b2_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
size_t v_x_5223__boxed_1278_; size_t v_x_5224__boxed_1279_; lean_object* v_res_1280_; 
v_x_5223__boxed_1278_ = lean_unbox_usize(v_x_1274_);
lean_dec(v_x_1274_);
v_x_5224__boxed_1279_ = lean_unbox_usize(v_x_1275_);
lean_dec(v_x_1275_);
v_res_1280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13(v_00_u03b2_1272_, v_x_1273_, v_x_5223__boxed_1278_, v_x_5224__boxed_1279_, v_x_1276_, v_x_1277_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1282_, v_x_1283_, v_x_1284_, v_x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object* v___x_1287_, lean_object* v_as_1288_, lean_object* v_k_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v___x_1287_, v_as_1288_, v_k_1289_, v_x_1290_, v_x_1291_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v___x_1295_, lean_object* v_as_1296_, lean_object* v_k_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(v___x_1295_, v_as_1296_, v_k_1297_, v_x_1298_, v_x_1299_, v_x_1300_, v_x_1301_);
lean_dec_ref(v_k_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16(lean_object* v_x_1303_, lean_object* v_keys_1304_, lean_object* v_v_1305_, lean_object* v_k_1306_, lean_object* v_as_1307_, lean_object* v_k_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___redArg(v_x_1303_, v_keys_1304_, v_v_1305_, v_k_1306_, v_as_1307_, v_k_1308_, v_x_1309_, v_x_1310_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16___boxed(lean_object* v_x_1314_, lean_object* v_keys_1315_, lean_object* v_v_1316_, lean_object* v_k_1317_, lean_object* v_as_1318_, lean_object* v_k_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__10_spec__16(v_x_1314_, v_keys_1315_, v_v_1316_, v_k_1317_, v_as_1318_, v_k_1319_, v_x_1320_, v_x_1321_, v_x_1322_, v_x_1323_);
lean_dec_ref(v_k_1319_);
lean_dec_ref(v_keys_1315_);
lean_dec(v_x_1314_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21(lean_object* v_00_u03b2_1325_, lean_object* v_n_1326_, lean_object* v_k_1327_, lean_object* v_v_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21___redArg(v_n_1326_, v_k_1327_, v_v_1328_);
return v___x_1329_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22(lean_object* v_00_u03b2_1330_, size_t v_depth_1331_, lean_object* v_keys_1332_, lean_object* v_vals_1333_, lean_object* v_heq_1334_, lean_object* v_i_1335_, lean_object* v_entries_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___redArg(v_depth_1331_, v_keys_1332_, v_vals_1333_, v_i_1335_, v_entries_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1331_ = stack[1].m_num;
lean_object* v_keys_1332_ = stack[2].m_obj;
lean_object* v_vals_1333_ = stack[3].m_obj;
lean_object* v_i_1335_ = stack[5].m_obj;
lean_object* v_entries_1336_ = stack[6].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22(lean_box(0), v_depth_1331_, v_keys_1332_, v_vals_1333_, lean_box(0), v_i_1335_, v_entries_1336_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22___boxed(lean_object* v_00_u03b2_1339_, lean_object* v_depth_1340_, lean_object* v_keys_1341_, lean_object* v_vals_1342_, lean_object* v_heq_1343_, lean_object* v_i_1344_, lean_object* v_entries_1345_){
_start:
{
size_t v_depth_boxed_1346_; lean_object* v_res_1347_; 
v_depth_boxed_1346_ = lean_unbox_usize(v_depth_1340_);
lean_dec(v_depth_1340_);
v_res_1347_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__22(v_00_u03b2_1339_, v_depth_boxed_1346_, v_keys_1341_, v_vals_1342_, v_heq_1343_, v_i_1344_, v_entries_1345_);
lean_dec_ref(v_vals_1342_);
lean_dec_ref(v_keys_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21_spec__22(lean_object* v_00_u03b2_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__13_spec__21_spec__22___redArg(v_x_1349_, v_x_1350_, v_x_1351_, v_x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object* v_s_1354_, lean_object* v_declName_1355_){
_start:
{
lean_object* v_pre_1356_; lean_object* v_eval_1357_; lean_object* v_post_1358_; lean_object* v_simprocNames_1359_; lean_object* v_erased_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1370_; 
v_pre_1356_ = lean_ctor_get(v_s_1354_, 0);
v_eval_1357_ = lean_ctor_get(v_s_1354_, 1);
v_post_1358_ = lean_ctor_get(v_s_1354_, 2);
v_simprocNames_1359_ = lean_ctor_get(v_s_1354_, 3);
v_erased_1360_ = lean_ctor_get(v_s_1354_, 4);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_s_1354_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1362_ = v_s_1354_;
v_isShared_1363_ = v_isSharedCheck_1370_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_erased_1360_);
lean_inc(v_simprocNames_1359_);
lean_inc(v_post_1358_);
lean_inc(v_eval_1357_);
lean_inc(v_pre_1356_);
lean_dec(v_s_1354_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1370_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1364_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_simprocNames_1359_, v_declName_1355_);
v___x_1365_ = lean_box(0);
v___x_1366_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_erased_1360_, v_declName_1355_, v___x_1365_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v___x_1366_);
lean_ctor_set(v___x_1362_, 3, v___x_1364_);
v___x_1368_ = v___x_1362_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_pre_1356_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_eval_1357_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_post_1358_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_unsigned_to_nat(16u);
v___x_1373_ = lean_mk_array(v___x_1372_, v___x_1371_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0);
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___x_1374_);
return v___x_1376_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default(void){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
return v___x_1379_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs(void){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
return v___x_1380_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
v___x_1383_ = lean_st_mk_ref(v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1385_;
v_res_1385_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1385_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
return v_res_1387_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object* v_a_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
uint8_t v___x_1390_; 
v___x_1390_ = 0;
return v___x_1390_;
}
else
{
lean_object* v_key_1391_; lean_object* v_tail_1392_; uint8_t v___x_1393_; 
v_key_1391_ = lean_ctor_get(v_x_1389_, 0);
v_tail_1392_ = lean_ctor_get(v_x_1389_, 2);
v___x_1393_ = lean_name_eq(v_key_1391_, v_a_1388_);
if (v___x_1393_ == 0)
{
v_x_1389_ = v_tail_1392_;
goto _start;
}
else
{
return v___x_1393_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1388_ = stack[0].m_obj;
lean_object* v_x_1389_ = stack[1].m_obj;
uint8_t v_res_1395_;
v_res_1395_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1388_, v_x_1389_);
stack->m_num = v_res_1395_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_a_1396_, lean_object* v_x_1397_){
_start:
{
uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_res_1398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1396_, v_x_1397_);
lean_dec(v_x_1397_);
lean_dec(v_a_1396_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object* v_m_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_buckets_1402_; lean_object* v___x_1403_; uint64_t v___y_1405_; 
v_buckets_1402_ = lean_ctor_get(v_m_1400_, 1);
v___x_1403_ = lean_array_get_size(v_buckets_1402_);
if (lean_obj_tag(v_a_1401_) == 0)
{
uint64_t v___x_1419_; 
v___x_1419_ = 1723ULL;
v___y_1405_ = v___x_1419_;
goto v___jp_1404_;
}
else
{
uint64_t v_hash_1420_; 
v_hash_1420_ = lean_ctor_get_uint64(v_a_1401_, sizeof(void*)*2);
v___y_1405_ = v_hash_1420_;
goto v___jp_1404_;
}
v___jp_1404_:
{
uint64_t v___x_1406_; uint64_t v___x_1407_; uint64_t v_fold_1408_; uint64_t v___x_1409_; uint64_t v___x_1410_; uint64_t v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1406_ = 32ULL;
v___x_1407_ = lean_uint64_shift_right(v___y_1405_, v___x_1406_);
v_fold_1408_ = lean_uint64_xor(v___y_1405_, v___x_1407_);
v___x_1409_ = 16ULL;
v___x_1410_ = lean_uint64_shift_right(v_fold_1408_, v___x_1409_);
v___x_1411_ = lean_uint64_xor(v_fold_1408_, v___x_1410_);
v___x_1412_ = lean_uint64_to_usize(v___x_1411_);
v___x_1413_ = lean_usize_of_nat(v___x_1403_);
v___x_1414_ = ((size_t)1ULL);
v___x_1415_ = lean_usize_sub(v___x_1413_, v___x_1414_);
v___x_1416_ = lean_usize_land(v___x_1412_, v___x_1415_);
v___x_1417_ = lean_array_uget_borrowed(v_buckets_1402_, v___x_1416_);
v___x_1418_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1401_, v___x_1417_);
return v___x_1418_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1400_ = stack[0].m_obj;
lean_object* v_a_1401_ = stack[1].m_obj;
uint8_t v_res_1421_;
v_res_1421_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1400_, v_a_1401_);
stack->m_num = v_res_1421_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object* v_m_1422_, lean_object* v_a_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_m_1422_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(lean_object* v_a_1426_, lean_object* v_b_1427_, lean_object* v_x_1428_){
_start:
{
if (lean_obj_tag(v_x_1428_) == 0)
{
lean_dec(v_b_1427_);
lean_dec(v_a_1426_);
return v_x_1428_;
}
else
{
lean_object* v_key_1429_; lean_object* v_value_1430_; lean_object* v_tail_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1443_; 
v_key_1429_ = lean_ctor_get(v_x_1428_, 0);
v_value_1430_ = lean_ctor_get(v_x_1428_, 1);
v_tail_1431_ = lean_ctor_get(v_x_1428_, 2);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1433_ = v_x_1428_;
v_isShared_1434_ = v_isSharedCheck_1443_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_tail_1431_);
lean_inc(v_value_1430_);
lean_inc(v_key_1429_);
lean_dec(v_x_1428_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1443_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_name_eq(v_key_1429_, v_a_1426_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1426_, v_b_1427_, v_tail_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 2, v___x_1436_);
v___x_1438_ = v___x_1433_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_key_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_value_1430_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
lean_object* v___x_1441_; 
lean_dec(v_value_1430_);
lean_dec(v_key_1429_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v_b_1427_);
lean_ctor_set(v___x_1433_, 0, v_a_1426_);
v___x_1441_ = v___x_1433_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1426_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_b_1427_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_tail_1431_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1444_, lean_object* v_x_1445_){
_start:
{
if (lean_obj_tag(v_x_1445_) == 0)
{
return v_x_1444_;
}
else
{
lean_object* v_key_1446_; lean_object* v_value_1447_; lean_object* v_tail_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1474_; 
v_key_1446_ = lean_ctor_get(v_x_1445_, 0);
v_value_1447_ = lean_ctor_get(v_x_1445_, 1);
v_tail_1448_ = lean_ctor_get(v_x_1445_, 2);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_x_1445_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1450_ = v_x_1445_;
v_isShared_1451_ = v_isSharedCheck_1474_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_tail_1448_);
lean_inc(v_value_1447_);
lean_inc(v_key_1446_);
lean_dec(v_x_1445_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1474_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; uint64_t v___y_1454_; 
v___x_1452_ = lean_array_get_size(v_x_1444_);
if (lean_obj_tag(v_key_1446_) == 0)
{
uint64_t v___x_1472_; 
v___x_1472_ = 1723ULL;
v___y_1454_ = v___x_1472_;
goto v___jp_1453_;
}
else
{
uint64_t v_hash_1473_; 
v_hash_1473_ = lean_ctor_get_uint64(v_key_1446_, sizeof(void*)*2);
v___y_1454_ = v_hash_1473_;
goto v___jp_1453_;
}
v___jp_1453_:
{
uint64_t v___x_1455_; uint64_t v___x_1456_; uint64_t v_fold_1457_; uint64_t v___x_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; size_t v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1455_ = 32ULL;
v___x_1456_ = lean_uint64_shift_right(v___y_1454_, v___x_1455_);
v_fold_1457_ = lean_uint64_xor(v___y_1454_, v___x_1456_);
v___x_1458_ = 16ULL;
v___x_1459_ = lean_uint64_shift_right(v_fold_1457_, v___x_1458_);
v___x_1460_ = lean_uint64_xor(v_fold_1457_, v___x_1459_);
v___x_1461_ = lean_uint64_to_usize(v___x_1460_);
v___x_1462_ = lean_usize_of_nat(v___x_1452_);
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_sub(v___x_1462_, v___x_1463_);
v___x_1465_ = lean_usize_land(v___x_1461_, v___x_1464_);
v___x_1466_ = lean_array_uget_borrowed(v_x_1444_, v___x_1465_);
lean_inc(v___x_1466_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 2, v___x_1466_);
v___x_1468_ = v___x_1450_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_key_1446_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_value_1447_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_array_uset(v_x_1444_, v___x_1465_, v___x_1468_);
v_x_1444_ = v___x_1469_;
v_x_1445_ = v_tail_1448_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1475_, lean_object* v_source_1476_, lean_object* v_target_1477_){
_start:
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_array_get_size(v_source_1476_);
v___x_1479_ = lean_nat_dec_lt(v_i_1475_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec_ref(v_source_1476_);
lean_dec(v_i_1475_);
return v_target_1477_;
}
else
{
lean_object* v_es_1480_; lean_object* v___x_1481_; lean_object* v_source_1482_; lean_object* v_target_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_es_1480_ = lean_array_fget(v_source_1476_, v_i_1475_);
v___x_1481_ = lean_box(0);
v_source_1482_ = lean_array_fset(v_source_1476_, v_i_1475_, v___x_1481_);
v_target_1483_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_target_1477_, v_es_1480_);
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_add(v_i_1475_, v___x_1484_);
lean_dec(v_i_1475_);
v_i_1475_ = v___x_1485_;
v_source_1476_ = v_source_1482_;
v_target_1477_ = v_target_1483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object* v_data_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_nbuckets_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1488_ = lean_array_get_size(v_data_1487_);
v___x_1489_ = lean_unsigned_to_nat(2u);
v_nbuckets_1490_ = lean_nat_mul(v___x_1488_, v___x_1489_);
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_mk_array(v_nbuckets_1490_, v___x_1492_);
v___x_1494_ = lean_array_propagate_mark(v_data_1487_, v___x_1493_);
v___x_1495_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v___x_1491_, v_data_1487_, v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object* v_m_1496_, lean_object* v_a_1497_, lean_object* v_b_1498_){
_start:
{
lean_object* v_size_1499_; lean_object* v_buckets_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1546_; 
v_size_1499_ = lean_ctor_get(v_m_1496_, 0);
v_buckets_1500_ = lean_ctor_get(v_m_1496_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v_m_1496_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1502_ = v_m_1496_;
v_isShared_1503_ = v_isSharedCheck_1546_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_buckets_1500_);
lean_inc(v_size_1499_);
lean_dec(v_m_1496_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1546_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; uint64_t v___y_1506_; 
v___x_1504_ = lean_array_get_size(v_buckets_1500_);
if (lean_obj_tag(v_a_1497_) == 0)
{
uint64_t v___x_1544_; 
v___x_1544_ = 1723ULL;
v___y_1506_ = v___x_1544_;
goto v___jp_1505_;
}
else
{
uint64_t v_hash_1545_; 
v_hash_1545_ = lean_ctor_get_uint64(v_a_1497_, sizeof(void*)*2);
v___y_1506_ = v_hash_1545_;
goto v___jp_1505_;
}
v___jp_1505_:
{
uint64_t v___x_1507_; uint64_t v___x_1508_; uint64_t v_fold_1509_; uint64_t v___x_1510_; uint64_t v___x_1511_; uint64_t v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; lean_object* v_bkt_1518_; uint8_t v___x_1519_; 
v___x_1507_ = 32ULL;
v___x_1508_ = lean_uint64_shift_right(v___y_1506_, v___x_1507_);
v_fold_1509_ = lean_uint64_xor(v___y_1506_, v___x_1508_);
v___x_1510_ = 16ULL;
v___x_1511_ = lean_uint64_shift_right(v_fold_1509_, v___x_1510_);
v___x_1512_ = lean_uint64_xor(v_fold_1509_, v___x_1511_);
v___x_1513_ = lean_uint64_to_usize(v___x_1512_);
v___x_1514_ = lean_usize_of_nat(v___x_1504_);
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_sub(v___x_1514_, v___x_1515_);
v___x_1517_ = lean_usize_land(v___x_1513_, v___x_1516_);
v_bkt_1518_ = lean_array_uget_borrowed(v_buckets_1500_, v___x_1517_);
v___x_1519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1497_, v_bkt_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v_size_x27_1521_; lean_object* v___x_1522_; lean_object* v_buckets_x27_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
v_size_x27_1521_ = lean_nat_add(v_size_1499_, v___x_1520_);
lean_dec(v_size_1499_);
lean_inc(v_bkt_1518_);
v___x_1522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1522_, 0, v_a_1497_);
lean_ctor_set(v___x_1522_, 1, v_b_1498_);
lean_ctor_set(v___x_1522_, 2, v_bkt_1518_);
v_buckets_x27_1523_ = lean_array_uset(v_buckets_1500_, v___x_1517_, v___x_1522_);
v___x_1524_ = lean_unsigned_to_nat(4u);
v___x_1525_ = lean_nat_mul(v_size_x27_1521_, v___x_1524_);
v___x_1526_ = lean_unsigned_to_nat(3u);
v___x_1527_ = lean_nat_div(v___x_1525_, v___x_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_array_get_size(v_buckets_x27_1523_);
v___x_1529_ = lean_nat_dec_le(v___x_1527_, v___x_1528_);
lean_dec(v___x_1527_);
if (v___x_1529_ == 0)
{
lean_object* v_val_1530_; lean_object* v___x_1532_; 
v_val_1530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_buckets_x27_1523_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v_val_1530_);
lean_ctor_set(v___x_1502_, 0, v_size_x27_1521_);
v___x_1532_ = v___x_1502_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_size_x27_1521_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_val_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
else
{
lean_object* v___x_1535_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v_buckets_x27_1523_);
lean_ctor_set(v___x_1502_, 0, v_size_x27_1521_);
v___x_1535_ = v___x_1502_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_size_x27_1521_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_buckets_x27_1523_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v_buckets_x27_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_inc(v_bkt_1518_);
v___x_1537_ = lean_box(0);
v_buckets_x27_1538_ = lean_array_uset(v_buckets_1500_, v___x_1517_, v___x_1537_);
v___x_1539_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1497_, v_b_1498_, v_bkt_1518_);
v___x_1540_ = lean_array_uset(v_buckets_x27_1538_, v___x_1517_, v___x_1539_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v___x_1540_);
v___x_1542_ = v___x_1502_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_size_1499_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0));
v___x_1549_ = lean_mk_io_user_error(v___x_1548_);
return v___x_1549_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object* v_declName_1552_, lean_object* v_keys_1553_, lean_object* v_proc_1554_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_initializing();
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref(v_proc_1554_);
lean_dec_ref(v_keys_1553_);
lean_dec(v_declName_1552_);
v___x_1557_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1);
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_keys_1561_; uint8_t v___x_1562_; 
v___x_1559_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_1560_ = lean_st_ref_get(v___x_1559_);
v_keys_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_ref(v_keys_1561_);
lean_dec(v___x_1560_);
v___x_1562_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_keys_1561_, v_declName_1552_);
lean_dec_ref(v_keys_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v_keys_1564_; lean_object* v_procs_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1576_; 
v___x_1563_ = lean_st_ref_take(v___x_1559_);
v_keys_1564_ = lean_ctor_get(v___x_1563_, 0);
v_procs_1565_ = lean_ctor_get(v___x_1563_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1567_ = v___x_1563_;
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_procs_1565_);
lean_inc(v_keys_1564_);
lean_dec(v___x_1563_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1576_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
lean_inc(v_declName_1552_);
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_keys_1564_, v_declName_1552_, v_keys_1553_);
v___x_1570_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_procs_1565_, v_declName_1552_, v_proc_1554_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 1, v___x_1570_);
lean_ctor_set(v___x_1567_, 0, v___x_1569_);
v___x_1572_ = v___x_1567_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_st_ref_put(v___x_1559_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec_ref(v_proc_1554_);
lean_dec_ref(v_keys_1553_);
v___x_1577_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2));
v___x_1578_ = l_Lean_privateToUserName(v_declName_1552_);
v___x_1579_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1578_, v___x_1562_);
v___x_1580_ = lean_string_append(v___x_1577_, v___x_1579_);
lean_dec_ref(v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_1582_ = lean_string_append(v___x_1580_, v___x_1581_);
v___x_1583_ = lean_mk_io_user_error(v___x_1582_);
v___x_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
return v___x_1584_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1552_ = stack[0].m_obj;
lean_object* v_keys_1553_ = stack[1].m_obj;
lean_object* v_proc_1554_ = stack[2].m_obj;
lean_object* v_res_1585_;
v_res_1585_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v_declName_1552_, v_keys_1553_, v_proc_1554_);
stack->m_obj
 = v_res_1585_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object* v_declName_1586_, lean_object* v_keys_1587_, lean_object* v_proc_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v_declName_1586_, v_keys_1587_, v_proc_1588_);
return v_res_1590_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object* v_00_u03b2_1591_, lean_object* v_m_1592_, lean_object* v_a_1593_){
_start:
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1592_, v_a_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1592_ = stack[1].m_obj;
lean_object* v_a_1593_ = stack[2].m_obj;
uint8_t v_res_1595_;
v_res_1595_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_box(0), v_m_1592_, v_a_1593_);
stack->m_num = v_res_1595_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object* v_00_u03b2_1596_, lean_object* v_m_1597_, lean_object* v_a_1598_){
_start:
{
uint8_t v_res_1599_; lean_object* v_r_1600_; 
v_res_1599_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(v_00_u03b2_1596_, v_m_1597_, v_a_1598_);
lean_dec(v_a_1598_);
lean_dec_ref(v_m_1597_);
v_r_1600_ = lean_box(v_res_1599_);
return v_r_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object* v_00_u03b2_1601_, lean_object* v_m_1602_, lean_object* v_a_1603_, lean_object* v_b_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1602_, v_a_1603_, v_b_1604_);
return v___x_1605_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object* v_00_u03b2_1606_, lean_object* v_a_1607_, lean_object* v_x_1608_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1607_, v_x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1607_ = stack[1].m_obj;
lean_object* v_x_1608_ = stack[2].m_obj;
uint8_t v_res_1610_;
v_res_1610_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_box(0), v_a_1607_, v_x_1608_);
stack->m_num = v_res_1610_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1611_, lean_object* v_a_1612_, lean_object* v_x_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(v_00_u03b2_1611_, v_a_1612_, v_x_1613_);
lean_dec(v_x_1613_);
lean_dec(v_a_1612_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object* v_00_u03b2_1616_, lean_object* v_data_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_data_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(lean_object* v_00_u03b2_1619_, lean_object* v_a_1620_, lean_object* v_b_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1620_, v_b_1621_, v_x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1624_, lean_object* v_i_1625_, lean_object* v_source_1626_, lean_object* v_target_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v_i_1625_, v_source_1626_, v_target_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1630_, v_x_1631_);
return v___x_1632_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object* v_d_u2081_1640_, lean_object* v_d_u2082_1641_){
_start:
{
lean_object* v_declName_1642_; lean_object* v_declName_1643_; uint8_t v___x_1644_; 
v_declName_1642_ = lean_ctor_get(v_d_u2081_1640_, 0);
v_declName_1643_ = lean_ctor_get(v_d_u2082_1641_, 0);
v___x_1644_ = l_Lean_Name_quickLt(v_declName_1642_, v_declName_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_u2081_1640_ = stack[0].m_obj;
lean_object* v_d_u2082_1641_ = stack[1].m_obj;
uint8_t v_res_1645_;
v_res_1645_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_1640_, v_d_u2082_1641_);
stack->m_num = v_res_1645_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object* v_d_u2081_1646_, lean_object* v_d_u2082_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_1646_, v_d_u2082_1647_);
lean_dec_ref(v_d_u2082_1647_);
lean_dec_ref(v_d_u2081_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
v___x_1653_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v___x_1652_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default(void){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState(void){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_s_1657_, lean_object* v_d_1658_){
_start:
{
lean_object* v_builtin_1659_; lean_object* v_newEntries_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1670_; 
v_builtin_1659_ = lean_ctor_get(v_s_1657_, 0);
v_newEntries_1660_ = lean_ctor_get(v_s_1657_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_s_1657_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1662_ = v_s_1657_;
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_newEntries_1660_);
lean_inc(v_builtin_1659_);
lean_dec(v_s_1657_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_declName_1664_; lean_object* v_keys_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v_declName_1664_ = lean_ctor_get(v_d_1658_, 0);
lean_inc(v_declName_1664_);
v_keys_1665_ = lean_ctor_get(v_d_1658_, 1);
lean_inc_ref(v_keys_1665_);
lean_dec_ref(v_d_1658_);
v___x_1666_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_1660_, v_declName_1664_, v_keys_1665_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1666_);
v___x_1668_ = v___x_1662_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_builtin_1659_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_result_1671_, lean_object* v_declName_1672_, lean_object* v_keys_1673_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v_declName_1672_);
lean_ctor_set(v___x_1674_, 1, v_keys_1673_);
v___x_1675_ = lean_array_push(v_result_1671_, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_1676_, lean_object* v_x1_1677_, lean_object* v_x2_1678_, lean_object* v_x3_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_apply_3(v_f_1676_, v_x1_1677_, v_x2_1678_, v_x3_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_1681_, lean_object* v_keys_1682_, lean_object* v_vals_1683_, lean_object* v_i_1684_, lean_object* v_acc_1685_){
_start:
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = lean_array_get_size(v_keys_1682_);
v___x_1687_ = lean_nat_dec_lt(v_i_1684_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_dec(v_i_1684_);
lean_dec(v_f_1681_);
return v_acc_1685_;
}
else
{
lean_object* v_k_1688_; lean_object* v_v_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_k_1688_ = lean_array_fget_borrowed(v_keys_1682_, v_i_1684_);
v_v_1689_ = lean_array_fget_borrowed(v_vals_1683_, v_i_1684_);
lean_inc(v_f_1681_);
lean_inc(v_v_1689_);
lean_inc(v_k_1688_);
v___x_1690_ = lean_apply_3(v_f_1681_, v_acc_1685_, v_k_1688_, v_v_1689_);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_nat_add(v_i_1684_, v___x_1691_);
lean_dec(v_i_1684_);
v_i_1684_ = v___x_1692_;
v_acc_1685_ = v___x_1690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_1694_, lean_object* v_keys_1695_, lean_object* v_vals_1696_, lean_object* v_i_1697_, lean_object* v_acc_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1694_, v_keys_1695_, v_vals_1696_, v_i_1697_, v_acc_1698_);
lean_dec_ref(v_vals_1696_);
lean_dec_ref(v_keys_1695_);
return v_res_1699_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1700_, lean_object* v_as_1701_, size_t v_i_1702_, size_t v_stop_1703_, lean_object* v_b_1704_){
_start:
{
lean_object* v___y_1706_; uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_eq(v_i_1702_, v_stop_1703_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_array_uget_borrowed(v_as_1701_, v_i_1702_);
switch(lean_obj_tag(v___x_1711_))
{
case 0:
{
lean_object* v_key_1712_; lean_object* v_val_1713_; lean_object* v___x_1714_; 
v_key_1712_ = lean_ctor_get(v___x_1711_, 0);
v_val_1713_ = lean_ctor_get(v___x_1711_, 1);
lean_inc(v_f_1700_);
lean_inc(v_val_1713_);
lean_inc(v_key_1712_);
v___x_1714_ = lean_apply_3(v_f_1700_, v_b_1704_, v_key_1712_, v_val_1713_);
v___y_1706_ = v___x_1714_;
goto v___jp_1705_;
}
case 1:
{
lean_object* v_node_1715_; lean_object* v___x_1716_; 
v_node_1715_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_f_1700_);
v___x_1716_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1700_, v_node_1715_, v_b_1704_);
v___y_1706_ = v___x_1716_;
goto v___jp_1705_;
}
default: 
{
v___y_1706_ = v_b_1704_;
goto v___jp_1705_;
}
}
}
else
{
lean_dec(v_f_1700_);
return v_b_1704_;
}
v___jp_1705_:
{
size_t v___x_1707_; size_t v___x_1708_; 
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_add(v_i_1702_, v___x_1707_);
v_i_1702_ = v___x_1708_;
v_b_1704_ = v___y_1706_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1700_ = stack[0].m_obj;
lean_object* v_as_1701_ = stack[1].m_obj;
size_t v_i_1702_ = stack[2].m_num;
size_t v_stop_1703_ = stack[3].m_num;
lean_object* v_b_1704_ = stack[4].m_obj;
lean_object* v_res_1717_;
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1700_, v_as_1701_, v_i_1702_, v_stop_1703_, v_b_1704_);
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
lean_object* v_es_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_es_1721_ = lean_ctor_get(v_x_1719_, 0);
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = lean_array_get_size(v_es_1721_);
v___x_1724_ = lean_nat_dec_lt(v___x_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_dec(v_f_1718_);
return v_x_1720_;
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = lean_usize_of_nat(v___x_1723_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1718_, v_es_1721_, v___x_1725_, v___x_1726_, v_x_1720_);
return v___x_1727_;
}
}
else
{
lean_object* v_ks_1728_; lean_object* v_vs_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_ks_1728_ = lean_ctor_get(v_x_1719_, 0);
v_vs_1729_ = lean_ctor_get(v_x_1719_, 1);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1718_, v_ks_1728_, v_vs_1729_, v___x_1730_, v_x_1720_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1732_, v_x_1733_, v_x_1734_);
lean_dec_ref(v_x_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1736_, lean_object* v_as_1737_, lean_object* v_i_1738_, lean_object* v_stop_1739_, lean_object* v_b_1740_){
_start:
{
size_t v_i_boxed_1741_; size_t v_stop_boxed_1742_; lean_object* v_res_1743_; 
v_i_boxed_1741_ = lean_unbox_usize(v_i_1738_);
lean_dec(v_i_1738_);
v_stop_boxed_1742_ = lean_unbox_usize(v_stop_1739_);
lean_dec(v_stop_1739_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1736_, v_as_1737_, v_i_boxed_1741_, v_stop_boxed_1742_, v_b_1740_);
lean_dec_ref(v_as_1737_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_1744_, lean_object* v_f_1745_, lean_object* v_init_1746_){
_start:
{
lean_object* v___f_1747_; lean_object* v___x_1748_; 
v___f_1747_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1747_, 0, v_f_1745_);
v___x_1748_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1747_, v_map_1744_, v_init_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_1749_, lean_object* v_f_1750_, lean_object* v_init_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1749_, v_f_1750_, v_init_1751_);
lean_dec_ref(v_map_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_hi_1753_, lean_object* v_pivot_1754_, lean_object* v_as_1755_, lean_object* v_i_1756_, lean_object* v_k_1757_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_nat_dec_lt(v_k_1757_, v_hi_1753_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_k_1757_);
v___x_1759_ = lean_array_fswap(v_as_1755_, v_i_1756_, v_hi_1753_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_i_1756_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_array_fget_borrowed(v_as_1755_, v_k_1757_);
v___x_1762_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1761_, v_pivot_1754_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_add(v_k_1757_, v___x_1763_);
lean_dec(v_k_1757_);
v_k_1757_ = v___x_1764_;
goto _start;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1766_ = lean_array_fswap(v_as_1755_, v_i_1756_, v_k_1757_);
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_nat_add(v_i_1756_, v___x_1767_);
lean_dec(v_i_1756_);
v___x_1769_ = lean_nat_add(v_k_1757_, v___x_1767_);
lean_dec(v_k_1757_);
v_as_1755_ = v___x_1766_;
v_i_1756_ = v___x_1768_;
v_k_1757_ = v___x_1769_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_hi_1771_, lean_object* v_pivot_1772_, lean_object* v_as_1773_, lean_object* v_i_1774_, lean_object* v_k_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1771_, v_pivot_1772_, v_as_1773_, v_i_1774_, v_k_1775_);
lean_dec_ref(v_pivot_1772_);
lean_dec(v_hi_1771_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object* v_n_1777_, lean_object* v_as_1778_, lean_object* v_lo_1779_, lean_object* v_hi_1780_){
_start:
{
lean_object* v___y_1782_; uint8_t v___x_1792_; 
v___x_1792_ = lean_nat_dec_lt(v_lo_1779_, v_hi_1780_);
if (v___x_1792_ == 0)
{
lean_dec(v_lo_1779_);
return v_as_1778_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v_mid_1795_; lean_object* v___y_1797_; lean_object* v___y_1803_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1793_ = lean_nat_add(v_lo_1779_, v_hi_1780_);
v___x_1794_ = lean_unsigned_to_nat(1u);
v_mid_1795_ = lean_nat_shiftr(v___x_1793_, v___x_1794_);
lean_dec(v___x_1793_);
v___x_1808_ = lean_array_fget_borrowed(v_as_1778_, v_mid_1795_);
v___x_1809_ = lean_array_fget_borrowed(v_as_1778_, v_lo_1779_);
v___x_1810_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
v___y_1803_ = v_as_1778_;
goto v___jp_1802_;
}
else
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_array_fswap(v_as_1778_, v_lo_1779_, v_mid_1795_);
v___y_1803_ = v___x_1811_;
goto v___jp_1802_;
}
v___jp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_array_fget_borrowed(v___y_1797_, v_mid_1795_);
v___x_1799_ = lean_array_fget_borrowed(v___y_1797_, v_hi_1780_);
v___x_1800_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec(v_mid_1795_);
v___y_1782_ = v___y_1797_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_array_fswap(v___y_1797_, v_mid_1795_, v_hi_1780_);
lean_dec(v_mid_1795_);
v___y_1782_ = v___x_1801_;
goto v___jp_1781_;
}
}
v___jp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = lean_array_fget_borrowed(v___y_1803_, v_hi_1780_);
v___x_1805_ = lean_array_fget_borrowed(v___y_1803_, v_lo_1779_);
v___x_1806_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
v___y_1797_ = v___y_1803_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_array_fswap(v___y_1803_, v_lo_1779_, v_hi_1780_);
v___y_1797_ = v___x_1807_;
goto v___jp_1796_;
}
}
}
v___jp_1781_:
{
lean_object* v_pivot_1783_; lean_object* v___x_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; uint8_t v___x_1787_; 
v_pivot_1783_ = lean_array_fget(v___y_1782_, v_hi_1780_);
lean_inc_n(v_lo_1779_, 2);
v___x_1784_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1780_, v_pivot_1783_, v___y_1782_, v_lo_1779_, v_lo_1779_);
lean_dec(v_pivot_1783_);
v_fst_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_fst_1785_);
v_snd_1786_ = lean_ctor_get(v___x_1784_, 1);
lean_inc(v_snd_1786_);
lean_dec_ref(v___x_1784_);
v___x_1787_ = lean_nat_dec_le(v_hi_1780_, v_fst_1785_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1777_, v_snd_1786_, v_lo_1779_, v_fst_1785_);
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_nat_add(v_fst_1785_, v___x_1789_);
lean_dec(v_fst_1785_);
v_as_1778_ = v___x_1788_;
v_lo_1779_ = v___x_1790_;
goto _start;
}
else
{
lean_dec(v_fst_1785_);
lean_dec(v_lo_1779_);
return v_snd_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_n_1812_, lean_object* v_as_1813_, lean_object* v_lo_1814_, lean_object* v_hi_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1812_, v_as_1813_, v_lo_1814_, v_hi_1815_);
lean_dec(v_hi_1815_);
lean_dec(v_n_1812_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1819_, lean_object* v_s_1820_){
_start:
{
lean_object* v_newEntries_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_result_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_newEntries_1821_ = lean_ctor_get(v_s_1820_, 1);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1824_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1821_, v___f_1819_, v___x_1823_);
v___x_1825_ = lean_array_get_size(v_result_1824_);
v___x_1826_ = lean_nat_dec_eq(v___x_1825_, v___x_1822_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___y_1830_; uint8_t v___x_1834_; 
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = lean_nat_sub(v___x_1825_, v___x_1827_);
v___x_1834_ = lean_nat_dec_le(v___x_1822_, v___x_1828_);
if (v___x_1834_ == 0)
{
lean_inc(v___x_1828_);
v___y_1830_ = v___x_1828_;
goto v___jp_1829_;
}
else
{
v___y_1830_ = v___x_1822_;
goto v___jp_1829_;
}
v___jp_1829_:
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_nat_dec_le(v___y_1830_, v___x_1828_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec(v___x_1828_);
lean_inc(v___y_1830_);
v___x_1832_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1825_, v_result_1824_, v___y_1830_, v___y_1830_);
lean_dec(v___y_1830_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; 
v___x_1833_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1825_, v_result_1824_, v___y_1830_, v___x_1828_);
lean_dec(v___x_1828_);
return v___x_1833_;
}
}
}
else
{
return v_result_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1835_, lean_object* v_s_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1835_, v_s_1836_);
lean_dec_ref(v_s_1836_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_x_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_box(0);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v_x_1840_);
lean_dec_ref(v_x_1840_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1842_, lean_object* v_x_1843_, lean_object* v_s_1844_){
_start:
{
lean_object* v_newEntries_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v_result_1848_; lean_object* v___x_1849_; lean_object* v___y_1851_; lean_object* v___y_1852_; uint8_t v___x_1855_; 
v_newEntries_1845_ = lean_ctor_get(v_s_1844_, 1);
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1848_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1845_, v___f_1842_, v___x_1847_);
v___x_1849_ = lean_array_get_size(v_result_1848_);
v___x_1855_ = lean_nat_dec_eq(v___x_1849_, v___x_1846_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___y_1859_; uint8_t v___x_1861_; 
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = lean_nat_sub(v___x_1849_, v___x_1856_);
v___x_1861_ = lean_nat_dec_le(v___x_1846_, v___x_1857_);
if (v___x_1861_ == 0)
{
lean_inc(v___x_1857_);
v___y_1859_ = v___x_1857_;
goto v___jp_1858_;
}
else
{
v___y_1859_ = v___x_1846_;
goto v___jp_1858_;
}
v___jp_1858_:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_nat_dec_le(v___y_1859_, v___x_1857_);
if (v___x_1860_ == 0)
{
lean_dec(v___x_1857_);
lean_inc(v___y_1859_);
v___y_1851_ = v___y_1859_;
v___y_1852_ = v___y_1859_;
goto v___jp_1850_;
}
else
{
v___y_1851_ = v___y_1859_;
v___y_1852_ = v___x_1857_;
goto v___jp_1850_;
}
}
}
else
{
lean_object* v___x_1862_; 
lean_inc_n(v_result_1848_, 2);
v___x_1862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1862_, 0, v_result_1848_);
lean_ctor_set(v___x_1862_, 1, v_result_1848_);
lean_ctor_set(v___x_1862_, 2, v_result_1848_);
return v___x_1862_;
}
v___jp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_1849_, v_result_1848_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_inc_ref_n(v___x_1853_, 2);
v___x_1854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
lean_ctor_set(v___x_1854_, 2, v___x_1853_);
return v___x_1854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1863_, lean_object* v_x_1864_, lean_object* v_s_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1863_, v_x_1864_, v_s_1865_);
lean_dec_ref(v_s_1865_);
lean_dec_ref(v_x_1864_);
return v_res_1866_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v_keys_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1879_; 
v___x_1869_ = lean_st_ref_get(v___x_1867_);
v_keys_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v___x_1869_, 1);
lean_dec(v_unused_1880_);
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_keys_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_keys_1870_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1867_ = stack[0].m_obj;
lean_object* v_res_1881_;
v_res_1881_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1867_);
stack->m_obj
 = v_res_1881_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1882_);
lean_dec(v___x_1882_);
return v_res_1884_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v_keys_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1899_; 
v___x_1889_ = lean_st_ref_get(v___x_1885_);
v_keys_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1889_, 1);
lean_dec(v_unused_1900_);
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1899_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_keys_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1899_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_keys_1890_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1885_ = stack[0].m_obj;
lean_object* v_x_1886_ = stack[1].m_obj;
lean_object* v___y_1887_ = stack[2].m_obj;
lean_object* v_res_1901_;
v_res_1901_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1885_, v_x_1886_, v___y_1887_);
stack->m_obj
 = v_res_1901_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1902_, lean_object* v_x_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1902_, v_x_1903_, v___y_1904_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_x_1903_);
lean_dec(v___x_1902_);
return v_res_1906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___f_1922_; 
v___x_1921_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1922_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1922_, 0, v___x_1921_);
return v___f_1922_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___f_1924_; 
v___x_1923_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1924_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_1924_, 0, v___x_1923_);
return v___f_1924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___f_1930_; lean_object* v___f_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1925_ = 0;
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_box(2);
v___f_1928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___f_1932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1934_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___f_1932_);
lean_ctor_set(v___x_1934_, 2, v___f_1931_);
lean_ctor_set(v___x_1934_, 3, v___f_1930_);
lean_ctor_set(v___x_1934_, 4, v___f_1929_);
lean_ctor_set(v___x_1934_, 5, v___f_1928_);
lean_ctor_set(v___x_1934_, 6, v___x_1927_);
lean_ctor_set(v___x_1934_, 7, v___x_1926_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*8, v___x_1925_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*8 + 1, v___x_1925_);
return v___x_1934_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___f_1935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1936_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___f_1935_);
return v___x_1937_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1940_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1941_;
v_res_1941_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_1944_, lean_object* v_00_u03b2_1945_, lean_object* v_map_1946_, lean_object* v_f_1947_, lean_object* v_init_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1946_, v_f_1947_, v_init_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_1950_, lean_object* v_00_u03b2_1951_, lean_object* v_map_1952_, lean_object* v_f_1953_, lean_object* v_init_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(v_00_u03c3_1950_, v_00_u03b2_1951_, v_map_1952_, v_f_1953_, v_init_1954_);
lean_dec_ref(v_map_1952_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object* v_n_1956_, lean_object* v_as_1957_, lean_object* v_lo_1958_, lean_object* v_hi_1959_, lean_object* v_w_1960_, lean_object* v_hlo_1961_, lean_object* v_hhi_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_1956_, v_as_1957_, v_lo_1958_, v_hi_1959_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1964_, lean_object* v_as_1965_, lean_object* v_lo_1966_, lean_object* v_hi_1967_, lean_object* v_w_1968_, lean_object* v_hlo_1969_, lean_object* v_hhi_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(v_n_1964_, v_as_1965_, v_lo_1966_, v_hi_1967_, v_w_1968_, v_hlo_1969_, v_hhi_1970_);
lean_dec(v_hi_1967_);
lean_dec(v_n_1964_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_1972_, lean_object* v_f_1973_, lean_object* v_init_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1973_, v_map_1972_, v_init_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_1976_, lean_object* v_f_1977_, lean_object* v_init_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1976_, v_f_1977_, v_init_1978_);
lean_dec_ref(v_map_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_1980_, lean_object* v_00_u03b2_1981_, lean_object* v_map_1982_, lean_object* v_f_1983_, lean_object* v_init_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1983_, v_map_1982_, v_init_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_1986_, lean_object* v_00_u03b2_1987_, lean_object* v_map_1988_, lean_object* v_f_1989_, lean_object* v_init_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1986_, v_00_u03b2_1987_, v_map_1988_, v_f_1989_, v_init_1990_);
lean_dec_ref(v_map_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_n_1992_, lean_object* v_lo_1993_, lean_object* v_hi_1994_, lean_object* v_hhi_1995_, lean_object* v_pivot_1996_, lean_object* v_as_1997_, lean_object* v_i_1998_, lean_object* v_k_1999_, lean_object* v_ilo_2000_, lean_object* v_ik_2001_, lean_object* v_w_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_1994_, v_pivot_1996_, v_as_1997_, v_i_1998_, v_k_1999_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_n_2004_, lean_object* v_lo_2005_, lean_object* v_hi_2006_, lean_object* v_hhi_2007_, lean_object* v_pivot_2008_, lean_object* v_as_2009_, lean_object* v_i_2010_, lean_object* v_k_2011_, lean_object* v_ilo_2012_, lean_object* v_ik_2013_, lean_object* v_w_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(v_n_2004_, v_lo_2005_, v_hi_2006_, v_hhi_2007_, v_pivot_2008_, v_as_2009_, v_i_2010_, v_k_2011_, v_ilo_2012_, v_ik_2013_, v_w_2014_);
lean_dec_ref(v_pivot_2008_);
lean_dec(v_hi_2006_);
lean_dec(v_lo_2005_);
lean_dec(v_n_2004_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2016_, lean_object* v_00_u03b1_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_f_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_2019_, v_x_2020_, v_x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2023_, lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_f_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_2023_, v_00_u03b1_2024_, v_00_u03b2_2025_, v_f_2026_, v_x_2027_, v_x_2028_);
lean_dec_ref(v_x_2027_);
return v_res_2029_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2030_, lean_object* v_00_u03b2_2031_, lean_object* v_00_u03c3_2032_, lean_object* v_f_2033_, lean_object* v_as_2034_, size_t v_i_2035_, size_t v_stop_2036_, lean_object* v_b_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_2033_, v_as_2034_, v_i_2035_, v_stop_2036_, v_b_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2033_ = stack[3].m_obj;
lean_object* v_as_2034_ = stack[4].m_obj;
size_t v_i_2035_ = stack[5].m_num;
size_t v_stop_2036_ = stack[6].m_num;
lean_object* v_b_2037_ = stack[7].m_obj;
lean_object* v_res_2039_;
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_box(0), lean_box(0), lean_box(0), v_f_2033_, v_as_2034_, v_i_2035_, v_stop_2036_, v_b_2037_);
stack->m_obj
 = v_res_2039_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_00_u03b2_2041_, lean_object* v_00_u03c3_2042_, lean_object* v_f_2043_, lean_object* v_as_2044_, lean_object* v_i_2045_, lean_object* v_stop_2046_, lean_object* v_b_2047_){
_start:
{
size_t v_i_boxed_2048_; size_t v_stop_boxed_2049_; lean_object* v_res_2050_; 
v_i_boxed_2048_ = lean_unbox_usize(v_i_2045_);
lean_dec(v_i_2045_);
v_stop_boxed_2049_ = lean_unbox_usize(v_stop_2046_);
lean_dec(v_stop_2046_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2040_, v_00_u03b2_2041_, v_00_u03c3_2042_, v_f_2043_, v_as_2044_, v_i_boxed_2048_, v_stop_boxed_2049_, v_b_2047_);
lean_dec_ref(v_as_2044_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_2051_, lean_object* v_00_u03b1_2052_, lean_object* v_00_u03b2_2053_, lean_object* v_f_2054_, lean_object* v_keys_2055_, lean_object* v_vals_2056_, lean_object* v_heq_2057_, lean_object* v_i_2058_, lean_object* v_acc_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_2054_, v_keys_2055_, v_vals_2056_, v_i_2058_, v_acc_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_2061_, lean_object* v_00_u03b1_2062_, lean_object* v_00_u03b2_2063_, lean_object* v_f_2064_, lean_object* v_keys_2065_, lean_object* v_vals_2066_, lean_object* v_heq_2067_, lean_object* v_i_2068_, lean_object* v_acc_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03c3_2061_, v_00_u03b1_2062_, v_00_u03b2_2063_, v_f_2064_, v_keys_2065_, v_vals_2066_, v_heq_2067_, v_i_2068_, v_acc_2069_);
lean_dec_ref(v_vals_2066_);
lean_dec_ref(v_keys_2065_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object* v_a_2071_, lean_object* v_x_2072_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_box(0);
return v___x_2073_;
}
else
{
lean_object* v_key_2074_; lean_object* v_value_2075_; lean_object* v_tail_2076_; uint8_t v___x_2077_; 
v_key_2074_ = lean_ctor_get(v_x_2072_, 0);
v_value_2075_ = lean_ctor_get(v_x_2072_, 1);
v_tail_2076_ = lean_ctor_get(v_x_2072_, 2);
v___x_2077_ = lean_name_eq(v_key_2074_, v_a_2071_);
if (v___x_2077_ == 0)
{
v_x_2072_ = v_tail_2076_;
goto _start;
}
else
{
lean_object* v___x_2079_; 
lean_inc(v_value_2075_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_value_2075_);
return v___x_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_2080_, lean_object* v_x_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_2080_, v_x_2081_);
lean_dec(v_x_2081_);
lean_dec(v_a_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object* v_m_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_buckets_2085_; lean_object* v___x_2086_; uint64_t v___y_2088_; 
v_buckets_2085_ = lean_ctor_get(v_m_2083_, 1);
v___x_2086_ = lean_array_get_size(v_buckets_2085_);
if (lean_obj_tag(v_a_2084_) == 0)
{
uint64_t v___x_2102_; 
v___x_2102_ = 1723ULL;
v___y_2088_ = v___x_2102_;
goto v___jp_2087_;
}
else
{
uint64_t v_hash_2103_; 
v_hash_2103_ = lean_ctor_get_uint64(v_a_2084_, sizeof(void*)*2);
v___y_2088_ = v_hash_2103_;
goto v___jp_2087_;
}
v___jp_2087_:
{
uint64_t v___x_2089_; uint64_t v___x_2090_; uint64_t v_fold_2091_; uint64_t v___x_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; size_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2089_ = 32ULL;
v___x_2090_ = lean_uint64_shift_right(v___y_2088_, v___x_2089_);
v_fold_2091_ = lean_uint64_xor(v___y_2088_, v___x_2090_);
v___x_2092_ = 16ULL;
v___x_2093_ = lean_uint64_shift_right(v_fold_2091_, v___x_2092_);
v___x_2094_ = lean_uint64_xor(v_fold_2091_, v___x_2093_);
v___x_2095_ = lean_uint64_to_usize(v___x_2094_);
v___x_2096_ = lean_usize_of_nat(v___x_2086_);
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_sub(v___x_2096_, v___x_2097_);
v___x_2099_ = lean_usize_land(v___x_2095_, v___x_2098_);
v___x_2100_ = lean_array_uget_borrowed(v_buckets_2085_, v___x_2099_);
v___x_2101_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_2084_, v___x_2100_);
return v___x_2101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* v_m_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_m_2104_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object* v_as_2107_, lean_object* v_k_2108_, lean_object* v_x_2109_, lean_object* v_x_2110_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_m_2113_; lean_object* v_a_2114_; uint8_t v___x_2115_; 
v___x_2111_ = lean_nat_add(v_x_2109_, v_x_2110_);
v___x_2112_ = lean_unsigned_to_nat(1u);
v_m_2113_ = lean_nat_shiftr(v___x_2111_, v___x_2112_);
lean_dec(v___x_2111_);
v_a_2114_ = lean_array_fget_borrowed(v_as_2107_, v_m_2113_);
v___x_2115_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_a_2114_, v_k_2108_);
if (v___x_2115_ == 0)
{
uint8_t v___x_2116_; 
lean_dec(v_x_2110_);
v___x_2116_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_k_2108_, v_a_2114_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec(v_m_2113_);
lean_dec(v_x_2109_);
lean_inc(v_a_2114_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v_a_2114_);
return v___x_2117_;
}
else
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_nat_dec_eq(v_m_2113_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = lean_nat_sub(v_m_2113_, v___x_2112_);
lean_dec(v_m_2113_);
v___x_2121_ = lean_nat_dec_lt(v___x_2120_, v_x_2109_);
if (v___x_2121_ == 0)
{
v_x_2110_ = v___x_2120_;
goto _start;
}
else
{
lean_object* v___x_2123_; 
lean_dec(v___x_2120_);
lean_dec(v_x_2109_);
v___x_2123_ = lean_box(0);
return v___x_2123_;
}
}
else
{
lean_object* v___x_2124_; 
lean_dec(v_m_2113_);
lean_dec(v_x_2109_);
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
}
}
else
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
lean_dec(v_x_2109_);
v___x_2125_ = lean_nat_add(v_m_2113_, v___x_2112_);
lean_dec(v_m_2113_);
v___x_2126_ = lean_nat_dec_le(v___x_2125_, v_x_2110_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_dec(v___x_2125_);
lean_dec(v_x_2110_);
v___x_2127_ = lean_box(0);
return v___x_2127_;
}
else
{
v_x_2109_ = v___x_2125_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object* v_as_2129_, lean_object* v_k_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2129_, v_k_2130_, v_x_2131_, v_x_2132_);
lean_dec_ref(v_k_2130_);
lean_dec_ref(v_as_2129_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_2134_, lean_object* v_vals_2135_, lean_object* v_i_2136_, lean_object* v_k_2137_){
_start:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = lean_array_get_size(v_keys_2134_);
v___x_2139_ = lean_nat_dec_lt(v_i_2136_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_dec(v_i_2136_);
v___x_2140_ = lean_box(0);
return v___x_2140_;
}
else
{
lean_object* v_k_x27_2141_; uint8_t v___x_2142_; 
v_k_x27_2141_ = lean_array_fget_borrowed(v_keys_2134_, v_i_2136_);
v___x_2142_ = lean_name_eq(v_k_2137_, v_k_x27_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_add(v_i_2136_, v___x_2143_);
lean_dec(v_i_2136_);
v_i_2136_ = v___x_2144_;
goto _start;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_array_fget_borrowed(v_vals_2135_, v_i_2136_);
lean_dec(v_i_2136_);
lean_inc(v___x_2146_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2148_, lean_object* v_vals_2149_, lean_object* v_i_2150_, lean_object* v_k_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2148_, v_vals_2149_, v_i_2150_, v_k_2151_);
lean_dec(v_k_2151_);
lean_dec_ref(v_vals_2149_);
lean_dec_ref(v_keys_2148_);
return v_res_2152_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object* v_x_2153_, size_t v_x_2154_, lean_object* v_x_2155_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
lean_object* v_es_2156_; lean_object* v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; lean_object* v_j_2160_; lean_object* v___x_2161_; 
v_es_2156_ = lean_ctor_get(v_x_2153_, 0);
v___x_2157_ = lean_box(2);
v___x_2158_ = ((size_t)31ULL);
v___x_2159_ = lean_usize_land(v_x_2154_, v___x_2158_);
v_j_2160_ = lean_usize_to_nat(v___x_2159_);
v___x_2161_ = lean_array_get_borrowed(v___x_2157_, v_es_2156_, v_j_2160_);
lean_dec(v_j_2160_);
switch(lean_obj_tag(v___x_2161_))
{
case 0:
{
lean_object* v_key_2162_; lean_object* v_val_2163_; uint8_t v___x_2164_; 
v_key_2162_ = lean_ctor_get(v___x_2161_, 0);
v_val_2163_ = lean_ctor_get(v___x_2161_, 1);
v___x_2164_ = lean_name_eq(v_x_2155_, v_key_2162_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_box(0);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; 
lean_inc(v_val_2163_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_val_2163_);
return v___x_2166_;
}
}
case 1:
{
lean_object* v_node_2167_; size_t v___x_2168_; size_t v___x_2169_; 
v_node_2167_ = lean_ctor_get(v___x_2161_, 0);
v___x_2168_ = ((size_t)5ULL);
v___x_2169_ = lean_usize_shift_right(v_x_2154_, v___x_2168_);
v_x_2153_ = v_node_2167_;
v_x_2154_ = v___x_2169_;
goto _start;
}
default: 
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
}
}
else
{
lean_object* v_ks_2172_; lean_object* v_vs_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_ks_2172_ = lean_ctor_get(v_x_2153_, 0);
v_vs_2173_ = lean_ctor_get(v_x_2153_, 1);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_ks_2172_, v_vs_2173_, v___x_2174_, v_x_2155_);
return v___x_2175_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2153_ = stack[0].m_obj;
size_t v_x_2154_ = stack[1].m_num;
lean_object* v_x_2155_ = stack[2].m_obj;
lean_object* v_res_2176_;
v_res_2176_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2153_, v_x_2154_, v_x_2155_);
stack->m_obj
 = v_res_2176_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_){
_start:
{
size_t v_x_1501__boxed_2180_; lean_object* v_res_2181_; 
v_x_1501__boxed_2180_ = lean_unbox_usize(v_x_2178_);
lean_dec(v_x_2178_);
v_res_2181_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2177_, v_x_1501__boxed_2180_, v_x_2179_);
lean_dec(v_x_2179_);
lean_dec_ref(v_x_2177_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
uint64_t v___y_2185_; 
if (lean_obj_tag(v_x_2183_) == 0)
{
uint64_t v___x_2188_; 
v___x_2188_ = 1723ULL;
v___y_2185_ = v___x_2188_;
goto v___jp_2184_;
}
else
{
uint64_t v_hash_2189_; 
v_hash_2189_ = lean_ctor_get_uint64(v_x_2183_, sizeof(void*)*2);
v___y_2185_ = v_hash_2189_;
goto v___jp_2184_;
}
v___jp_2184_:
{
size_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_uint64_to_usize(v___y_2185_);
v___x_2187_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2182_, v___x_2186_, v_x_2183_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2190_, v_x_2191_);
lean_dec(v_x_2191_);
lean_dec_ref(v_x_2190_);
return v_res_2192_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object* v_declName_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_env_2198_; lean_object* v___x_2209_; 
v___x_2196_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2197_ = lean_st_ref_get(v_a_2194_);
v_env_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc_ref(v_env_2198_);
lean_dec(v___x_2197_);
v___x_2209_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2198_, v_declName_2193_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2210_; lean_object* v_toEnvExtension_2211_; lean_object* v_asyncMode_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v_newEntries_2216_; lean_object* v___x_2217_; 
v___x_2210_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2211_ = lean_ctor_get(v___x_2210_, 0);
v_asyncMode_2212_ = lean_ctor_get(v_toEnvExtension_2211_, 2);
v___x_2213_ = lean_box(0);
v___x_2214_ = 0;
lean_inc_ref(v_env_2198_);
v___x_2215_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2196_, v___x_2210_, v_env_2198_, v_asyncMode_2212_, v___x_2213_, v___x_2214_);
v_newEntries_2216_ = lean_ctor_get(v___x_2215_, 1);
lean_inc_ref(v_newEntries_2216_);
lean_dec(v___x_2215_);
v___x_2217_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_2216_, v_declName_2193_);
lean_dec_ref(v_newEntries_2216_);
if (lean_obj_tag(v___x_2217_) == 1)
{
lean_object* v___x_2218_; 
lean_dec_ref(v_env_2198_);
lean_dec(v_declName_2193_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
return v___x_2218_;
}
else
{
lean_dec(v___x_2217_);
goto v___jp_2199_;
}
}
else
{
lean_object* v_val_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2247_; 
v_val_2219_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2221_ = v___x_2209_;
v_isShared_2222_ = v_isSharedCheck_2247_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_val_2219_);
lean_dec(v___x_2209_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2247_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2223_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v___x_2224_ = 0;
v___x_2225_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2196_, v___x_2223_, v_env_2198_, v_val_2219_, v___x_2224_);
lean_dec(v_val_2219_);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_array_get_size(v___x_2225_);
v___x_2228_ = lean_nat_dec_lt(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_dec_ref(v___x_2225_);
lean_del_object(v___x_2221_);
goto v___jp_2199_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_sub(v___x_2227_, v___x_2229_);
v___x_2231_ = lean_nat_dec_le(v___x_2226_, v___x_2230_);
if (v___x_2231_ == 0)
{
lean_dec(v___x_2230_);
lean_dec_ref(v___x_2225_);
lean_del_object(v___x_2221_);
goto v___jp_2199_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0));
lean_inc(v_declName_2193_);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_declName_2193_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v___x_2225_, v___x_2233_, v___x_2226_, v___x_2230_);
lean_dec_ref_known(v___x_2233_, 2);
lean_dec_ref(v___x_2225_);
if (lean_obj_tag(v___x_2234_) == 1)
{
lean_object* v_val_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_env_2198_);
lean_dec(v_declName_2193_);
v_val_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_val_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2246_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_keys_2239_; lean_object* v___x_2241_; 
v_keys_2239_ = lean_ctor_get(v_val_2235_, 1);
lean_inc_ref(v_keys_2239_);
lean_dec(v_val_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v_keys_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_keys_2239_);
v___x_2241_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2243_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2241_);
v___x_2243_ = v___x_2221_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_dec(v___x_2234_);
lean_del_object(v___x_2221_);
goto v___jp_2199_;
}
}
}
}
}
v___jp_2199_:
{
lean_object* v___x_2200_; lean_object* v_toEnvExtension_2201_; lean_object* v_asyncMode_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v_builtin_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2200_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2201_ = lean_ctor_get(v___x_2200_, 0);
v_asyncMode_2202_ = lean_ctor_get(v_toEnvExtension_2201_, 2);
v___x_2203_ = lean_box(0);
v___x_2204_ = 0;
v___x_2205_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2196_, v___x_2200_, v_env_2198_, v_asyncMode_2202_, v___x_2203_, v___x_2204_);
v_builtin_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc_ref(v_builtin_2206_);
lean_dec(v___x_2205_);
v___x_2207_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_2206_, v_declName_2193_);
lean_dec(v_declName_2193_);
lean_dec_ref(v_builtin_2206_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2193_ = stack[0].m_obj;
lean_object* v_a_2194_ = stack[1].m_obj;
lean_object* v_res_2248_;
v_res_2248_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2193_, v_a_2194_);
stack->m_obj
 = v_res_2248_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object* v_declName_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2249_, v_a_2250_);
lean_dec(v_a_2250_);
return v_res_2252_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object* v_declName_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2253_, v_a_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2253_ = stack[0].m_obj;
lean_object* v_a_2254_ = stack[1].m_obj;
lean_object* v_a_2255_ = stack[2].m_obj;
lean_object* v_res_2258_;
v_res_2258_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_2253_, v_a_2254_, v_a_2255_);
stack->m_obj
 = v_res_2258_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object* v_declName_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_2259_, v_a_2260_, v_a_2261_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object* v_00_u03b2_2264_, lean_object* v_m_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2265_, v_a_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object* v_00_u03b2_2268_, lean_object* v_m_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(v_00_u03b2_2268_, v_m_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_m_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object* v_00_u03b2_2272_, lean_object* v_x_2273_, lean_object* v_x_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2273_, v_x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object* v_00_u03b2_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(v_00_u03b2_2276_, v_x_2277_, v_x_2278_);
lean_dec(v_x_2278_);
lean_dec_ref(v_x_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object* v_as_2280_, lean_object* v_k_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2280_, v_k_2281_, v_x_2282_, v_x_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object* v_as_2286_, lean_object* v_k_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(v_as_2286_, v_k_2287_, v_x_2288_, v_x_2289_, v_x_2290_);
lean_dec_ref(v_k_2287_);
lean_dec_ref(v_as_2286_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2292_, lean_object* v_a_2293_, lean_object* v_x_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_2293_, v_x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2296_, lean_object* v_a_2297_, lean_object* v_x_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(v_00_u03b2_2296_, v_a_2297_, v_x_2298_);
lean_dec(v_x_2298_);
lean_dec(v_a_2297_);
return v_res_2299_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2300_, lean_object* v_x_2301_, size_t v_x_2302_, lean_object* v_x_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2301_, v_x_2302_, v_x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2301_ = stack[1].m_obj;
size_t v_x_2302_ = stack[2].m_num;
lean_object* v_x_2303_ = stack[3].m_obj;
lean_object* v_res_2305_;
v_res_2305_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_box(0), v_x_2301_, v_x_2302_, v_x_2303_);
stack->m_obj
 = v_res_2305_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
size_t v_x_1788__boxed_2310_; lean_object* v_res_2311_; 
v_x_1788__boxed_2310_ = lean_unbox_usize(v_x_2308_);
lean_dec(v_x_2308_);
v_res_2311_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_2306_, v_x_2307_, v_x_1788__boxed_2310_, v_x_2309_);
lean_dec(v_x_2309_);
lean_dec_ref(v_x_2307_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2312_, lean_object* v_keys_2313_, lean_object* v_vals_2314_, lean_object* v_heq_2315_, lean_object* v_i_2316_, lean_object* v_k_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2313_, v_vals_2314_, v_i_2316_, v_k_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2319_, lean_object* v_keys_2320_, lean_object* v_vals_2321_, lean_object* v_heq_2322_, lean_object* v_i_2323_, lean_object* v_k_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(v_00_u03b2_2319_, v_keys_2320_, v_vals_2321_, v_heq_2322_, v_i_2323_, v_k_2324_);
lean_dec(v_k_2324_);
lean_dec_ref(v_vals_2321_);
lean_dec_ref(v_keys_2320_);
return v_res_2325_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object* v_declName_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2344_; 
v___x_2329_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2326_, v_a_2327_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2344_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2344_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
if (lean_obj_tag(v_a_2330_) == 0)
{
uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2334_ = 0;
v___x_2335_ = lean_box(v___x_2334_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
else
{
uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
lean_dec_ref_known(v_a_2330_, 1);
v___x_2339_ = 1;
v___x_2340_ = lean_box(v___x_2339_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2340_);
v___x_2342_ = v___x_2332_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2326_ = stack[0].m_obj;
lean_object* v_a_2327_ = stack[1].m_obj;
lean_object* v_res_2345_;
v_res_2345_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2326_, v_a_2327_);
stack->m_obj
 = v_res_2345_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object* v_declName_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2346_, v_a_2347_);
lean_dec(v_a_2347_);
return v_res_2349_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object* v_declName_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2350_, v_a_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isCbvSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2350_ = stack[0].m_obj;
lean_object* v_a_2351_ = stack[1].m_obj;
lean_object* v_a_2352_ = stack[2].m_obj;
lean_object* v_res_2355_;
v_res_2355_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_2350_, v_a_2351_, v_a_2352_);
stack->m_obj
 = v_res_2355_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object* v_declName_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_2356_, v_a_2357_, v_a_2358_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2360_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object* v_declName_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_env_2366_; lean_object* v___x_2367_; lean_object* v_toEnvExtension_2368_; lean_object* v_asyncMode_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v_builtin_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2364_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2365_ = lean_st_ref_get(v_a_2362_);
v_env_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc_ref(v_env_2366_);
lean_dec(v___x_2365_);
v___x_2367_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2368_ = lean_ctor_get(v___x_2367_, 0);
v_asyncMode_2369_ = lean_ctor_get(v_toEnvExtension_2368_, 2);
v___x_2370_ = lean_box(0);
v___x_2371_ = 0;
v___x_2372_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2364_, v___x_2367_, v_env_2366_, v_asyncMode_2369_, v___x_2370_, v___x_2371_);
v_builtin_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc_ref(v_builtin_2373_);
lean_dec(v___x_2372_);
v___x_2374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_builtin_2373_, v_declName_2361_);
lean_dec_ref(v_builtin_2373_);
v___x_2375_ = lean_box(v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2361_ = stack[0].m_obj;
lean_object* v_a_2362_ = stack[1].m_obj;
lean_object* v_res_2377_;
v_res_2377_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2361_, v_a_2362_);
stack->m_obj
 = v_res_2377_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object* v_declName_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec(v_declName_2378_);
return v_res_2381_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object* v_declName_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2382_, v_a_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2382_ = stack[0].m_obj;
lean_object* v_a_2383_ = stack[1].m_obj;
lean_object* v_a_2384_ = stack[2].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_2382_, v_a_2383_, v_a_2384_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object* v_declName_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_declName_2388_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object* v_declName_2393_, lean_object* v_keys_2394_, lean_object* v_ps_2395_){
_start:
{
lean_object* v_state_2396_; lean_object* v_importedEntries_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2414_; 
v_state_2396_ = lean_ctor_get(v_ps_2395_, 1);
v_importedEntries_2397_ = lean_ctor_get(v_ps_2395_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_ps_2395_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2399_ = v_ps_2395_;
v_isShared_2400_ = v_isSharedCheck_2414_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_state_2396_);
lean_inc(v_importedEntries_2397_);
lean_dec(v_ps_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2414_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_builtin_2401_; lean_object* v_newEntries_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2413_; 
v_builtin_2401_ = lean_ctor_get(v_state_2396_, 0);
v_newEntries_2402_ = lean_ctor_get(v_state_2396_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_state_2396_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2404_ = v_state_2396_;
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_newEntries_2402_);
lean_inc(v_builtin_2401_);
lean_dec(v_state_2396_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_2402_, v_declName_2393_, v_keys_2394_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 1, v___x_2406_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_builtin_2401_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v___x_2408_);
v___x_2410_ = v___x_2399_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_importedEntries_2397_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2418_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
lean_ctor_set(v___x_2420_, 2, v___x_2419_);
lean_ctor_set(v___x_2420_, 3, v___x_2419_);
lean_ctor_set(v___x_2420_, 4, v___x_2418_);
lean_ctor_set(v___x_2420_, 5, v___x_2418_);
lean_ctor_set(v___x_2420_, 6, v___x_2418_);
lean_ctor_set(v___x_2420_, 7, v___x_2418_);
lean_ctor_set(v___x_2420_, 8, v___x_2418_);
lean_ctor_set(v___x_2420_, 9, v___x_2418_);
lean_ctor_set(v___x_2420_, 10, v___x_2418_);
lean_ctor_set(v___x_2420_, 11, v___x_2417_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2421_ = lean_unsigned_to_nat(32u);
v___x_2422_ = lean_mk_empty_array_with_capacity(v___x_2421_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2424_ = ((size_t)5ULL);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_unsigned_to_nat(32u);
v___x_2427_ = lean_mk_empty_array_with_capacity(v___x_2426_);
v___x_2428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2429_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2427_);
lean_ctor_set(v___x_2429_, 2, v___x_2425_);
lean_ctor_set(v___x_2429_, 3, v___x_2425_);
lean_ctor_set_usize(v___x_2429_, 4, v___x_2424_);
return v___x_2429_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2430_ = lean_box(1);
v___x_2431_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3);
v___x_2432_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_2433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v___x_2431_);
lean_ctor_set(v___x_2433_, 2, v___x_2430_);
return v___x_2433_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object* v_msgData_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2438_; lean_object* v_toCold_2439_; lean_object* v_env_2440_; lean_object* v_options_2441_; uint8_t v___x_2442_; lean_object* v_env_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2438_ = lean_st_ref_get(v___y_2436_);
v_toCold_2439_ = lean_ctor_get(v___y_2435_, 0);
v_env_2440_ = lean_ctor_get(v___x_2438_, 0);
lean_inc_ref(v_env_2440_);
lean_dec(v___x_2438_);
v_options_2441_ = lean_ctor_get(v_toCold_2439_, 2);
v___x_2442_ = 0;
v_env_2443_ = l_Lean_Environment_setRecordingDeps(v_env_2440_, v___x_2442_);
v___x_2444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2445_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2441_);
v___x_2446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2446_, 0, v_env_2443_);
lean_ctor_set(v___x_2446_, 1, v___x_2444_);
lean_ctor_set(v___x_2446_, 2, v___x_2445_);
lean_ctor_set(v___x_2446_, 3, v_options_2441_);
v___x_2447_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v_msgData_2434_);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2434_ = stack[0].m_obj;
lean_object* v___y_2435_ = stack[1].m_obj;
lean_object* v___y_2436_ = stack[2].m_obj;
lean_object* v_res_2449_;
v_res_2449_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_2434_, v___y_2435_, v___y_2436_);
stack->m_obj
 = v_res_2449_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object* v_msgData_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
return v_res_2454_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object* v_msg_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_ref_2459_; lean_object* v___x_2460_; lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2469_; 
v_ref_2459_ = lean_ctor_get(v___y_2456_, 2);
v___x_2460_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msg_2455_, v___y_2456_, v___y_2457_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_inc(v_ref_2459_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_ref_2459_);
lean_ctor_set(v___x_2465_, 1, v_a_2461_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 1);
lean_ctor_set(v___x_2463_, 0, v___x_2465_);
v___x_2467_ = v___x_2463_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2455_ = stack[0].m_obj;
lean_object* v___y_2456_ = stack[1].m_obj;
lean_object* v___y_2457_ = stack[2].m_obj;
lean_object* v_res_2470_;
v_res_2470_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2455_, v___y_2456_, v___y_2457_);
stack->m_obj
 = v_res_2470_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object* v_msg_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2475_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___redArg___closed__0);
v___x_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
return v___x_2479_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2));
v___x_2482_ = l_Lean_stringToMessageData(v___x_2481_);
return v___x_2482_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_2484_ = l_Lean_stringToMessageData(v___x_2483_);
return v___x_2484_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5));
v___x_2487_ = l_Lean_stringToMessageData(v___x_2486_);
return v___x_2487_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object* v_declName_2488_, lean_object* v_keys_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v_nextMacroScope_2494_; lean_object* v_ngen_2495_; lean_object* v_auxDeclNGen_2496_; lean_object* v_traceState_2497_; lean_object* v_recordedDeps_2498_; lean_object* v_messages_2499_; lean_object* v_infoState_2500_; lean_object* v_snapshotTasks_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___f_2509_; lean_object* v___y_2511_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___x_2553_; lean_object* v_env_2554_; lean_object* v___x_2555_; 
lean_inc(v_declName_2488_);
v___f_2509_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0), 3, 2);
lean_closure_set(v___f_2509_, 0, v_declName_2488_);
lean_closure_set(v___f_2509_, 1, v_keys_2489_);
v___x_2553_ = lean_st_ref_get(v_a_2491_);
v_env_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc_ref(v_env_2554_);
lean_dec(v___x_2553_);
v___x_2555_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2554_, v_declName_2488_);
lean_dec_ref(v_env_2554_);
if (lean_obj_tag(v___x_2555_) == 0)
{
v___y_2533_ = v_a_2490_;
v___y_2534_ = v_a_2491_;
goto v___jp_2532_;
}
else
{
uint8_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec_ref_known(v___x_2555_, 1);
lean_dec_ref(v___f_2509_);
v___x_2556_ = 0;
v___x_2557_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3);
v___x_2558_ = l_Lean_MessageData_ofConstName(v_declName_2488_, v___x_2556_);
v___x_2559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6);
v___x_2561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2561_, v_a_2490_, v_a_2491_);
return v___x_2562_;
}
v___jp_2493_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
v___x_2506_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2506_, 0, v___y_2504_);
lean_ctor_set(v___x_2506_, 1, v_nextMacroScope_2494_);
lean_ctor_set(v___x_2506_, 2, v_ngen_2495_);
lean_ctor_set(v___x_2506_, 3, v_auxDeclNGen_2496_);
lean_ctor_set(v___x_2506_, 4, v_traceState_2497_);
lean_ctor_set(v___x_2506_, 5, v___x_2505_);
lean_ctor_set(v___x_2506_, 6, v_recordedDeps_2498_);
lean_ctor_set(v___x_2506_, 7, v_messages_2499_);
lean_ctor_set(v___x_2506_, 8, v_infoState_2500_);
lean_ctor_set(v___x_2506_, 9, v_snapshotTasks_2501_);
v___x_2507_ = lean_st_ref_put(v___y_2502_, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___y_2503_);
return v___x_2508_;
}
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v_env_2513_; lean_object* v_nextMacroScope_2514_; lean_object* v_ngen_2515_; lean_object* v_auxDeclNGen_2516_; lean_object* v_traceState_2517_; lean_object* v_recordedDeps_2518_; lean_object* v_messages_2519_; lean_object* v_infoState_2520_; lean_object* v_snapshotTasks_2521_; lean_object* v___x_2522_; lean_object* v_toEnvExtension_2523_; lean_object* v_asyncMode_2524_; uint8_t v_logWrites_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2512_ = lean_st_ref_take(v___y_2511_);
v_env_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc_ref(v_env_2513_);
v_nextMacroScope_2514_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_nextMacroScope_2514_);
v_ngen_2515_ = lean_ctor_get(v___x_2512_, 2);
lean_inc_ref(v_ngen_2515_);
v_auxDeclNGen_2516_ = lean_ctor_get(v___x_2512_, 3);
lean_inc_ref(v_auxDeclNGen_2516_);
v_traceState_2517_ = lean_ctor_get(v___x_2512_, 4);
lean_inc_ref(v_traceState_2517_);
v_recordedDeps_2518_ = lean_ctor_get(v___x_2512_, 6);
lean_inc_ref(v_recordedDeps_2518_);
v_messages_2519_ = lean_ctor_get(v___x_2512_, 7);
lean_inc_ref(v_messages_2519_);
v_infoState_2520_ = lean_ctor_get(v___x_2512_, 8);
lean_inc_ref(v_infoState_2520_);
v_snapshotTasks_2521_ = lean_ctor_get(v___x_2512_, 9);
lean_inc_ref(v_snapshotTasks_2521_);
lean_dec(v___x_2512_);
v___x_2522_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2523_ = lean_ctor_get(v___x_2522_, 0);
v_asyncMode_2524_ = lean_ctor_get(v_toEnvExtension_2523_, 2);
v_logWrites_2525_ = lean_ctor_get_uint8(v_toEnvExtension_2523_, sizeof(void*)*6);
v___x_2526_ = lean_box(0);
v___x_2527_ = lean_box(0);
v___x_2528_ = 1;
if (v_logWrites_2525_ == 0)
{
lean_object* v___x_2529_; 
lean_inc_ref(v_toEnvExtension_2523_);
v___x_2529_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2523_, v_env_2513_, v___f_2509_, v_asyncMode_2524_, v___x_2527_, v___x_2528_);
v_nextMacroScope_2494_ = v_nextMacroScope_2514_;
v_ngen_2495_ = v_ngen_2515_;
v_auxDeclNGen_2496_ = v_auxDeclNGen_2516_;
v_traceState_2497_ = v_traceState_2517_;
v_recordedDeps_2498_ = v_recordedDeps_2518_;
v_messages_2499_ = v_messages_2519_;
v_infoState_2500_ = v_infoState_2520_;
v_snapshotTasks_2501_ = v_snapshotTasks_2521_;
v___y_2502_ = v___y_2511_;
v___y_2503_ = v___x_2526_;
v___y_2504_ = v___x_2529_;
goto v___jp_2493_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_inc_ref_n(v_toEnvExtension_2523_, 2);
v___x_2530_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2523_, v_env_2513_);
lean_dec_ref(v_env_2513_);
v___x_2531_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2523_, v___x_2530_, v___f_2509_, v_asyncMode_2524_, v___x_2527_, v___x_2528_);
v_nextMacroScope_2494_ = v_nextMacroScope_2514_;
v_ngen_2495_ = v_ngen_2515_;
v_auxDeclNGen_2496_ = v_auxDeclNGen_2516_;
v_traceState_2497_ = v_traceState_2517_;
v_recordedDeps_2498_ = v_recordedDeps_2518_;
v_messages_2499_ = v_messages_2519_;
v_infoState_2500_ = v_infoState_2520_;
v_snapshotTasks_2501_ = v_snapshotTasks_2521_;
v___y_2502_ = v___y_2511_;
v___y_2503_ = v___x_2526_;
v___y_2504_ = v___x_2531_;
goto v___jp_2493_;
}
}
v___jp_2532_:
{
lean_object* v___x_2535_; 
lean_inc(v_declName_2488_);
v___x_2535_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2488_, v___y_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; uint8_t v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
if (v___x_2537_ == 0)
{
lean_dec(v_declName_2488_);
v___y_2511_ = v___y_2534_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec_ref(v___f_2509_);
v___x_2538_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3);
v___x_2539_ = 0;
v___x_2540_ = l_Lean_MessageData_ofConstName(v_declName_2488_, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2538_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2543_, v___y_2533_, v___y_2534_);
return v___x_2544_;
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v___f_2509_);
lean_dec(v_declName_2488_);
v_a_2545_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2535_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2535_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_registerCbvSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2488_ = stack[0].m_obj;
lean_object* v_keys_2489_ = stack[1].m_obj;
lean_object* v_a_2490_ = stack[2].m_obj;
lean_object* v_a_2491_ = stack[3].m_obj;
lean_object* v_res_2563_;
v_res_2563_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_declName_2488_, v_keys_2489_, v_a_2490_, v_a_2491_);
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object* v_declName_2564_, lean_object* v_keys_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_declName_2564_, v_keys_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
return v_res_2569_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object* v_00_u03b1_2570_, lean_object* v_msg_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2571_, v___y_2572_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2571_ = stack[1].m_obj;
lean_object* v___y_2572_ = stack[2].m_obj;
lean_object* v___y_2573_ = stack[3].m_obj;
lean_object* v_res_2576_;
v_res_2576_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_box(0), v_msg_2571_, v___y_2572_, v___y_2573_);
stack->m_obj
 = v_res_2576_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object* v_00_u03b1_2577_, lean_object* v_msg_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(v_00_u03b1_2577_, v_msg_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
return v_res_2582_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object* v_e_2583_){
_start:
{
if (lean_obj_tag(v_e_2583_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
v_a_2585_ = lean_ctor_get(v_e_2583_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_e_2583_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2587_ = v_e_2583_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v_e_2583_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = lean_mk_io_user_error(v_a_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 1);
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
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
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_a_2594_ = lean_ctor_get(v_e_2583_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_e_2583_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v_e_2583_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v_e_2583_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 0);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2583_ = stack[0].m_obj;
lean_object* v_res_2602_;
v_res_2602_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2583_);
stack->m_obj
 = v_res_2602_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2603_);
return v_res_2605_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object* v_00_u03b1_2606_, lean_object* v_e_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2607_);
return v___x_2609_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2607_ = stack[1].m_obj;
lean_object* v_res_2610_;
v_res_2610_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_box(0), v_e_2607_);
stack->m_obj
 = v_res_2610_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_2611_, lean_object* v_e_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(v_00_u03b1_2611_, v_e_2612_);
return v_res_2614_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object* v_declName_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v_env_2625_; lean_object* v_opts_2626_; uint8_t v___x_2627_; lean_object* v___x_2628_; 
v_env_2625_ = lean_ctor_get(v_a_2623_, 0);
v_opts_2626_ = lean_ctor_get(v_a_2623_, 1);
v___x_2627_ = 0;
lean_inc(v_declName_2622_);
lean_inc_ref(v_env_2625_);
v___x_2628_ = l_Lean_Environment_find_x3f(v_env_2625_, v_declName_2622_, v___x_2627_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2629_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0));
v___x_2630_ = 1;
v___x_2631_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2622_, v___x_2630_);
v___x_2632_ = lean_string_append(v___x_2629_, v___x_2631_);
lean_dec_ref(v___x_2631_);
v___x_2633_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2634_ = lean_string_append(v___x_2632_, v___x_2633_);
v___x_2635_ = lean_mk_io_user_error(v___x_2634_);
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
return v___x_2636_;
}
else
{
lean_object* v_val_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2682_; 
v_val_2637_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2639_ = v___x_2628_;
v_isShared_2640_ = v_isSharedCheck_2682_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_val_2637_);
lean_dec(v___x_2628_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2682_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_ConstantInfo_type(v_val_2637_);
if (lean_obj_tag(v___x_2658_) == 4)
{
lean_object* v_declName_2659_; 
v_declName_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_declName_2659_);
lean_dec_ref_known(v___x_2658_, 2);
if (lean_obj_tag(v_declName_2659_) == 1)
{
lean_object* v_pre_2660_; 
v_pre_2660_ = lean_ctor_get(v_declName_2659_, 0);
lean_inc(v_pre_2660_);
if (lean_obj_tag(v_pre_2660_) == 1)
{
lean_object* v_pre_2661_; 
v_pre_2661_ = lean_ctor_get(v_pre_2660_, 0);
lean_inc(v_pre_2661_);
if (lean_obj_tag(v_pre_2661_) == 1)
{
lean_object* v_pre_2662_; 
v_pre_2662_ = lean_ctor_get(v_pre_2661_, 0);
lean_inc(v_pre_2662_);
if (lean_obj_tag(v_pre_2662_) == 1)
{
lean_object* v_pre_2663_; 
v_pre_2663_ = lean_ctor_get(v_pre_2662_, 0);
lean_inc(v_pre_2663_);
if (lean_obj_tag(v_pre_2663_) == 1)
{
lean_object* v_pre_2664_; 
v_pre_2664_ = lean_ctor_get(v_pre_2663_, 0);
if (lean_obj_tag(v_pre_2664_) == 0)
{
lean_object* v_str_2665_; lean_object* v_str_2666_; lean_object* v_str_2667_; lean_object* v_str_2668_; lean_object* v_str_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_str_2665_ = lean_ctor_get(v_declName_2659_, 1);
lean_inc_ref(v_str_2665_);
lean_dec_ref_known(v_declName_2659_, 2);
v_str_2666_ = lean_ctor_get(v_pre_2660_, 1);
lean_inc_ref(v_str_2666_);
lean_dec_ref_known(v_pre_2660_, 2);
v_str_2667_ = lean_ctor_get(v_pre_2661_, 1);
lean_inc_ref(v_str_2667_);
lean_dec_ref_known(v_pre_2661_, 2);
v_str_2668_ = lean_ctor_get(v_pre_2662_, 1);
lean_inc_ref(v_str_2668_);
lean_dec_ref_known(v_pre_2662_, 2);
v_str_2669_ = lean_ctor_get(v_pre_2663_, 1);
lean_inc_ref(v_str_2669_);
lean_dec_ref_known(v_pre_2663_, 2);
v___x_2670_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0));
v___x_2671_ = lean_string_dec_eq(v_str_2669_, v___x_2670_);
lean_dec_ref(v_str_2669_);
if (v___x_2671_ == 0)
{
lean_dec_ref(v_str_2668_);
lean_dec_ref(v_str_2667_);
lean_dec_ref(v_str_2666_);
lean_dec_ref(v_str_2665_);
goto v___jp_2641_;
}
else
{
lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___x_2672_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1));
v___x_2673_ = lean_string_dec_eq(v_str_2668_, v___x_2672_);
lean_dec_ref(v_str_2668_);
if (v___x_2673_ == 0)
{
lean_dec_ref(v_str_2667_);
lean_dec_ref(v_str_2666_);
lean_dec_ref(v_str_2665_);
goto v___jp_2641_;
}
else
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4));
v___x_2675_ = lean_string_dec_eq(v_str_2667_, v___x_2674_);
lean_dec_ref(v_str_2667_);
if (v___x_2675_ == 0)
{
lean_dec_ref(v_str_2666_);
lean_dec_ref(v_str_2665_);
goto v___jp_2641_;
}
else
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5));
v___x_2677_ = lean_string_dec_eq(v_str_2666_, v___x_2676_);
lean_dec_ref(v_str_2666_);
if (v___x_2677_ == 0)
{
lean_dec_ref(v_str_2665_);
goto v___jp_2641_;
}
else
{
lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2678_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6));
v___x_2679_ = lean_string_dec_eq(v_str_2665_, v___x_2678_);
lean_dec_ref(v_str_2665_);
if (v___x_2679_ == 0)
{
goto v___jp_2641_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_del_object(v___x_2639_);
lean_dec(v_val_2637_);
v___x_2680_ = l_Lean_Environment_evalConst___redArg(v_env_2625_, v_opts_2626_, v_declName_2622_, v___x_2679_);
lean_dec(v_declName_2622_);
v___x_2681_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v___x_2680_);
return v___x_2681_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2663_, 2);
lean_dec_ref_known(v_pre_2662_, 2);
lean_dec_ref_known(v_pre_2661_, 2);
lean_dec_ref_known(v_pre_2660_, 2);
lean_dec_ref_known(v_declName_2659_, 2);
goto v___jp_2641_;
}
}
else
{
lean_dec_ref_known(v_pre_2662_, 2);
lean_dec(v_pre_2663_);
lean_dec_ref_known(v_pre_2661_, 2);
lean_dec_ref_known(v_pre_2660_, 2);
lean_dec_ref_known(v_declName_2659_, 2);
goto v___jp_2641_;
}
}
else
{
lean_dec(v_pre_2662_);
lean_dec_ref_known(v_pre_2661_, 2);
lean_dec_ref_known(v_pre_2660_, 2);
lean_dec_ref_known(v_declName_2659_, 2);
goto v___jp_2641_;
}
}
else
{
lean_dec_ref_known(v_pre_2660_, 2);
lean_dec(v_pre_2661_);
lean_dec_ref_known(v_declName_2659_, 2);
goto v___jp_2641_;
}
}
else
{
lean_dec_ref_known(v_declName_2659_, 2);
lean_dec(v_pre_2660_);
goto v___jp_2641_;
}
}
else
{
lean_dec(v_declName_2659_);
goto v___jp_2641_;
}
}
else
{
lean_dec_ref(v___x_2658_);
goto v___jp_2641_;
}
v___jp_2641_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2642_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2));
v___x_2643_ = l_Lean_privateToUserName(v_declName_2622_);
v___x_2644_ = 1;
v___x_2645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2643_, v___x_2644_);
v___x_2646_ = lean_string_append(v___x_2642_, v___x_2645_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3));
v___x_2648_ = lean_string_append(v___x_2646_, v___x_2647_);
v___x_2649_ = l_Lean_ConstantInfo_type(v_val_2637_);
lean_dec(v_val_2637_);
v___x_2650_ = lean_expr_dbg_to_string(v___x_2649_);
lean_dec_ref(v___x_2649_);
v___x_2651_ = lean_string_append(v___x_2648_, v___x_2650_);
lean_dec_ref(v___x_2650_);
v___x_2652_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2653_ = lean_string_append(v___x_2651_, v___x_2652_);
v___x_2654_ = lean_mk_io_user_error(v___x_2653_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v___x_2654_);
v___x_2656_ = v___x_2639_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2622_ = stack[0].m_obj;
lean_object* v_a_2623_ = stack[1].m_obj;
lean_object* v_res_2683_;
v_res_2683_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2622_, v_a_2623_);
stack->m_obj
 = v_res_2683_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object* v_declName_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2684_, v_a_2685_);
lean_dec_ref(v_a_2685_);
return v_res_2687_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object* v_e_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_declName_2691_; lean_object* v___x_2692_; 
v_declName_2691_ = lean_ctor_get(v_e_2688_, 0);
lean_inc(v_declName_2691_);
v___x_2692_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2691_, v_a_2689_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2701_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_e_2688_);
lean_ctor_set(v___x_2697_, 1, v_a_2693_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2697_);
v___x_2699_ = v___x_2695_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_e_2688_);
v_a_2702_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2692_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2692_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2688_ = stack[0].m_obj;
lean_object* v_a_2689_ = stack[1].m_obj;
lean_object* v_res_2710_;
v_res_2710_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_2688_, v_a_2689_);
stack->m_obj
 = v_res_2710_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object* v_e_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_2711_, v_a_2712_);
lean_dec_ref(v_a_2712_);
return v_res_2714_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1);
v___x_2717_ = lean_st_mk_ref(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2719_;
v_res_2719_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2719_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___y_2722_){
_start:
{
lean_inc_ref(v___y_2722_);
return v___y_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___y_2723_);
lean_dec_ref(v___y_2723_);
return v_res_2724_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2725_ = stack[0].m_obj;
lean_object* v___y_2726_ = stack[1].m_obj;
lean_object* v___y_2727_ = stack[2].m_obj;
lean_object* v_res_2730_;
v_res_2730_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2725_, v___y_2726_, v___y_2727_);
stack->m_obj
 = v_res_2730_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2731_, v___y_2732_, v___y_2733_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_x_2731_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_e_2736_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2737_; 
v_toCbvSimprocOLeanEntry_2737_ = lean_ctor_get(v_e_2736_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2737_);
return v_toCbvSimprocOLeanEntry_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_e_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_e_2738_);
lean_dec_ref(v_e_2738_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_s_2740_, lean_object* v_e_2741_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2742_; lean_object* v_proc_2743_; lean_object* v_declName_2744_; uint8_t v_phase_2745_; lean_object* v_keys_2746_; lean_object* v___x_2747_; 
v_toCbvSimprocOLeanEntry_2742_ = lean_ctor_get(v_e_2741_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2742_);
v_proc_2743_ = lean_ctor_get(v_e_2741_, 1);
lean_inc_ref(v_proc_2743_);
lean_dec_ref(v_e_2741_);
v_declName_2744_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2742_, 0);
lean_inc(v_declName_2744_);
v_phase_2745_ = lean_ctor_get_uint8(v_toCbvSimprocOLeanEntry_2742_, sizeof(void*)*2);
v_keys_2746_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2742_, 1);
lean_inc_ref(v_keys_2746_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_2742_);
v___x_2747_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_2740_, v_keys_2746_, v_declName_2744_, v_phase_2745_, v_proc_2743_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_a_2749_);
lean_inc_ref_n(v___x_2750_, 2);
v___x_2751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2752_, v_a_2753_);
lean_dec_ref(v_x_2752_);
return v_res_2754_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___x_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_st_ref_get(v___x_2755_);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2755_ = stack[0].m_obj;
lean_object* v_res_2759_;
v_res_2759_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_2755_);
stack->m_obj
 = v_res_2759_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___x_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_2760_);
lean_dec(v___x_2760_);
return v_res_2762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___f_2772_; 
v___x_2771_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___f_2772_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2772_, 0, v___x_2771_);
return v___f_2772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2773_; uint8_t v___x_2774_; lean_object* v___f_2775_; lean_object* v___f_2776_; lean_object* v___f_2777_; lean_object* v___f_2778_; lean_object* v___f_2779_; lean_object* v___f_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = 0;
v___f_2775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___x_2782_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v___f_2780_);
lean_ctor_set(v___x_2782_, 2, v___f_2779_);
lean_ctor_set(v___x_2782_, 3, v___f_2778_);
lean_ctor_set(v___x_2782_, 4, v___f_2777_);
lean_ctor_set(v___x_2782_, 5, v___f_2776_);
lean_ctor_set(v___x_2782_, 6, v___f_2775_);
lean_ctor_set(v___x_2782_, 7, v___x_2773_);
lean_ctor_set_uint8(v___x_2782_, sizeof(void*)*8, v___x_2774_);
lean_ctor_set_uint8(v___x_2782_, sizeof(void*)*8 + 1, v___x_2774_);
return v___x_2782_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2785_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2786_;
v_res_2786_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2786_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object* v_declName_2789_, lean_object* v_s_2790_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(v_s_2790_, v_declName_2789_);
return v___x_2791_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2792_, lean_object* v_i_2793_, lean_object* v_k_2794_){
_start:
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = lean_array_get_size(v_keys_2792_);
v___x_2796_ = lean_nat_dec_lt(v_i_2793_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_dec(v_i_2793_);
return v___x_2796_;
}
else
{
lean_object* v_k_x27_2797_; uint8_t v___x_2798_; 
v_k_x27_2797_ = lean_array_fget_borrowed(v_keys_2792_, v_i_2793_);
v___x_2798_ = lean_name_eq(v_k_2794_, v_k_x27_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_unsigned_to_nat(1u);
v___x_2800_ = lean_nat_add(v_i_2793_, v___x_2799_);
lean_dec(v_i_2793_);
v_i_2793_ = v___x_2800_;
goto _start;
}
else
{
lean_dec(v_i_2793_);
return v___x_2796_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2792_ = stack[0].m_obj;
lean_object* v_i_2793_ = stack[1].m_obj;
lean_object* v_k_2794_ = stack[2].m_obj;
uint8_t v_res_2802_;
v_res_2802_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2792_, v_i_2793_, v_k_2794_);
stack->m_num = v_res_2802_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2803_, lean_object* v_i_2804_, lean_object* v_k_2805_){
_start:
{
uint8_t v_res_2806_; lean_object* v_r_2807_; 
v_res_2806_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2803_, v_i_2804_, v_k_2805_);
lean_dec(v_k_2805_);
lean_dec_ref(v_keys_2803_);
v_r_2807_ = lean_box(v_res_2806_);
return v_r_2807_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object* v_x_2808_, size_t v_x_2809_, lean_object* v_x_2810_){
_start:
{
if (lean_obj_tag(v_x_2808_) == 0)
{
lean_object* v_es_2811_; lean_object* v___x_2812_; size_t v___x_2813_; size_t v___x_2814_; lean_object* v_j_2815_; lean_object* v___x_2816_; 
v_es_2811_ = lean_ctor_get(v_x_2808_, 0);
v___x_2812_ = lean_box(2);
v___x_2813_ = ((size_t)31ULL);
v___x_2814_ = lean_usize_land(v_x_2809_, v___x_2813_);
v_j_2815_ = lean_usize_to_nat(v___x_2814_);
v___x_2816_ = lean_array_get_borrowed(v___x_2812_, v_es_2811_, v_j_2815_);
lean_dec(v_j_2815_);
switch(lean_obj_tag(v___x_2816_))
{
case 0:
{
lean_object* v_key_2817_; uint8_t v___x_2818_; 
v_key_2817_ = lean_ctor_get(v___x_2816_, 0);
v___x_2818_ = lean_name_eq(v_x_2810_, v_key_2817_);
return v___x_2818_;
}
case 1:
{
lean_object* v_node_2819_; size_t v___x_2820_; size_t v___x_2821_; 
v_node_2819_ = lean_ctor_get(v___x_2816_, 0);
v___x_2820_ = ((size_t)5ULL);
v___x_2821_ = lean_usize_shift_right(v_x_2809_, v___x_2820_);
v_x_2808_ = v_node_2819_;
v_x_2809_ = v___x_2821_;
goto _start;
}
default: 
{
uint8_t v___x_2823_; 
v___x_2823_ = 0;
return v___x_2823_;
}
}
}
else
{
lean_object* v_ks_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_ks_2824_ = lean_ctor_get(v_x_2808_, 0);
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_2824_, v___x_2825_, v_x_2810_);
return v___x_2826_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2808_ = stack[0].m_obj;
size_t v_x_2809_ = stack[1].m_num;
lean_object* v_x_2810_ = stack[2].m_obj;
uint8_t v_res_2827_;
v_res_2827_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2808_, v_x_2809_, v_x_2810_);
stack->m_num = v_res_2827_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_2828_, lean_object* v_x_2829_, lean_object* v_x_2830_){
_start:
{
size_t v_x_503__boxed_2831_; uint8_t v_res_2832_; lean_object* v_r_2833_; 
v_x_503__boxed_2831_ = lean_unbox_usize(v_x_2829_);
lean_dec(v_x_2829_);
v_res_2832_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2828_, v_x_503__boxed_2831_, v_x_2830_);
lean_dec(v_x_2830_);
lean_dec_ref(v_x_2828_);
v_r_2833_ = lean_box(v_res_2832_);
return v_r_2833_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object* v_x_2834_, lean_object* v_x_2835_){
_start:
{
uint64_t v___y_2837_; 
if (lean_obj_tag(v_x_2835_) == 0)
{
uint64_t v___x_2840_; 
v___x_2840_ = 1723ULL;
v___y_2837_ = v___x_2840_;
goto v___jp_2836_;
}
else
{
uint64_t v_hash_2841_; 
v_hash_2841_ = lean_ctor_get_uint64(v_x_2835_, sizeof(void*)*2);
v___y_2837_ = v_hash_2841_;
goto v___jp_2836_;
}
v___jp_2836_:
{
size_t v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = lean_uint64_to_usize(v___y_2837_);
v___x_2839_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2834_, v___x_2838_, v_x_2835_);
return v___x_2839_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2834_ = stack[0].m_obj;
lean_object* v_x_2835_ = stack[1].m_obj;
uint8_t v_res_2842_;
v_res_2842_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2834_, v_x_2835_);
stack->m_num = v_res_2842_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
uint8_t v_res_2845_; lean_object* v_r_2846_; 
v_res_2845_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2843_, v_x_2844_);
lean_dec(v_x_2844_);
lean_dec_ref(v_x_2843_);
v_r_2846_ = lean_box(v_res_2845_);
return v_r_2846_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
return v___x_2848_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1));
v___x_2851_ = l_Lean_stringToMessageData(v___x_2850_);
return v___x_2851_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object* v_declName_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v_env_2859_; lean_object* v___x_2860_; lean_object* v___y_2862_; lean_object* v_ext_2886_; lean_object* v_toEnvExtension_2887_; lean_object* v_asyncMode_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; lean_object* v_simprocNames_2891_; uint8_t v___x_2892_; 
lean_inc(v_declName_2852_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0), 2, 1);
lean_closure_set(v___f_2856_, 0, v_declName_2852_);
v___x_2857_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_2858_ = lean_st_ref_get(v_a_2854_);
v_env_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc_ref(v_env_2859_);
lean_dec(v___x_2858_);
v___x_2860_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_2886_ = lean_ctor_get(v___x_2860_, 1);
v_toEnvExtension_2887_ = lean_ctor_get(v_ext_2886_, 0);
v_asyncMode_2888_ = lean_ctor_get(v_toEnvExtension_2887_, 2);
v___x_2889_ = 0;
v___x_2890_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2857_, v___x_2860_, v_env_2859_, v_asyncMode_2888_, v___x_2889_);
v_simprocNames_2891_ = lean_ctor_get(v___x_2890_, 3);
lean_inc_ref(v_simprocNames_2891_);
lean_dec(v___x_2890_);
v___x_2892_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_simprocNames_2891_, v_declName_2852_);
lean_dec_ref(v_simprocNames_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec_ref(v___f_2856_);
v___x_2893_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0);
v___x_2894_ = l_Lean_MessageData_ofConstName(v_declName_2852_, v___x_2889_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2893_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2897_, v_a_2853_, v_a_2854_);
return v___x_2898_;
}
else
{
lean_dec(v_declName_2852_);
v___y_2862_ = v_a_2854_;
goto v___jp_2861_;
}
v___jp_2861_:
{
lean_object* v___x_2863_; lean_object* v_env_2864_; lean_object* v_nextMacroScope_2865_; lean_object* v_ngen_2866_; lean_object* v_auxDeclNGen_2867_; lean_object* v_traceState_2868_; lean_object* v_recordedDeps_2869_; lean_object* v_messages_2870_; lean_object* v_infoState_2871_; lean_object* v_snapshotTasks_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2884_; 
v___x_2863_ = lean_st_ref_take(v___y_2862_);
v_env_2864_ = lean_ctor_get(v___x_2863_, 0);
v_nextMacroScope_2865_ = lean_ctor_get(v___x_2863_, 1);
v_ngen_2866_ = lean_ctor_get(v___x_2863_, 2);
v_auxDeclNGen_2867_ = lean_ctor_get(v___x_2863_, 3);
v_traceState_2868_ = lean_ctor_get(v___x_2863_, 4);
v_recordedDeps_2869_ = lean_ctor_get(v___x_2863_, 6);
v_messages_2870_ = lean_ctor_get(v___x_2863_, 7);
v_infoState_2871_ = lean_ctor_get(v___x_2863_, 8);
v_snapshotTasks_2872_ = lean_ctor_get(v___x_2863_, 9);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2863_, 5);
lean_dec(v_unused_2885_);
v___x_2874_ = v___x_2863_;
v_isShared_2875_ = v_isSharedCheck_2884_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_snapshotTasks_2872_);
lean_inc(v_infoState_2871_);
lean_inc(v_messages_2870_);
lean_inc(v_recordedDeps_2869_);
lean_inc(v_traceState_2868_);
lean_inc(v_auxDeclNGen_2867_);
lean_inc(v_ngen_2866_);
lean_inc(v_nextMacroScope_2865_);
lean_inc(v_env_2864_);
lean_dec(v___x_2863_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2884_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2876_ = lean_box(0);
v___x_2877_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2860_, v_env_2864_, v___f_2856_);
v___x_2878_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 5, v___x_2878_);
lean_ctor_set(v___x_2874_, 0, v___x_2877_);
v___x_2880_ = v___x_2874_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_nextMacroScope_2865_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_ngen_2866_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v_auxDeclNGen_2867_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v_traceState_2868_);
lean_ctor_set(v_reuseFailAlloc_2883_, 5, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2883_, 6, v_recordedDeps_2869_);
lean_ctor_set(v_reuseFailAlloc_2883_, 7, v_messages_2870_);
lean_ctor_set(v_reuseFailAlloc_2883_, 8, v_infoState_2871_);
lean_ctor_set(v_reuseFailAlloc_2883_, 9, v_snapshotTasks_2872_);
v___x_2880_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_st_ref_put(v___y_2862_, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2876_);
return v___x_2882_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2852_ = stack[0].m_obj;
lean_object* v_a_2853_ = stack[1].m_obj;
lean_object* v_a_2854_ = stack[2].m_obj;
lean_object* v_res_2899_;
v_res_2899_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_2852_, v_a_2853_, v_a_2854_);
stack->m_obj
 = v_res_2899_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object* v_declName_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2904_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object* v_00_u03b2_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
uint8_t v___x_2908_; 
v___x_2908_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2906_, v_x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2906_ = stack[1].m_obj;
lean_object* v_x_2907_ = stack[2].m_obj;
uint8_t v_res_2909_;
v_res_2909_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_box(0), v_x_2906_, v_x_2907_);
stack->m_num = v_res_2909_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object* v_00_u03b2_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_){
_start:
{
uint8_t v_res_2913_; lean_object* v_r_2914_; 
v_res_2913_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(v_00_u03b2_2910_, v_x_2911_, v_x_2912_);
lean_dec(v_x_2912_);
lean_dec_ref(v_x_2911_);
v_r_2914_ = lean_box(v_res_2913_);
return v_r_2914_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object* v_00_u03b2_2915_, lean_object* v_x_2916_, size_t v_x_2917_, lean_object* v_x_2918_){
_start:
{
uint8_t v___x_2919_; 
v___x_2919_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2916_, v_x_2917_, v_x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2916_ = stack[1].m_obj;
size_t v_x_2917_ = stack[2].m_num;
lean_object* v_x_2918_ = stack[3].m_obj;
uint8_t v_res_2920_;
v_res_2920_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_box(0), v_x_2916_, v_x_2917_, v_x_2918_);
stack->m_num = v_res_2920_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
size_t v_x_724__boxed_2925_; uint8_t v_res_2926_; lean_object* v_r_2927_; 
v_x_724__boxed_2925_ = lean_unbox_usize(v_x_2923_);
lean_dec(v_x_2923_);
v_res_2926_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(v_00_u03b2_2921_, v_x_2922_, v_x_724__boxed_2925_, v_x_2924_);
lean_dec(v_x_2924_);
lean_dec_ref(v_x_2922_);
v_r_2927_ = lean_box(v_res_2926_);
return v_r_2927_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2928_, lean_object* v_keys_2929_, lean_object* v_vals_2930_, lean_object* v_heq_2931_, lean_object* v_i_2932_, lean_object* v_k_2933_){
_start:
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2929_, v_i_2932_, v_k_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2929_ = stack[1].m_obj;
lean_object* v_vals_2930_ = stack[2].m_obj;
lean_object* v_i_2932_ = stack[4].m_obj;
lean_object* v_k_2933_ = stack[5].m_obj;
uint8_t v_res_2935_;
v_res_2935_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_box(0), v_keys_2929_, v_vals_2930_, lean_box(0), v_i_2932_, v_k_2933_);
stack->m_num = v_res_2935_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2936_, lean_object* v_keys_2937_, lean_object* v_vals_2938_, lean_object* v_heq_2939_, lean_object* v_i_2940_, lean_object* v_k_2941_){
_start:
{
uint8_t v_res_2942_; lean_object* v_r_2943_; 
v_res_2942_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_2936_, v_keys_2937_, v_vals_2938_, v_heq_2939_, v_i_2940_, v_k_2941_);
lean_dec(v_k_2941_);
lean_dec_ref(v_vals_2938_);
lean_dec_ref(v_keys_2937_);
v_r_2943_ = lean_box(v_res_2942_);
return v_r_2943_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object* v_ext_2944_, lean_object* v_b_2945_, uint8_t v_kind_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_toCold_2950_; lean_object* v_currNamespace_2951_; lean_object* v___x_2952_; lean_object* v_env_2953_; lean_object* v_nextMacroScope_2954_; lean_object* v_ngen_2955_; lean_object* v_auxDeclNGen_2956_; lean_object* v_traceState_2957_; lean_object* v_recordedDeps_2958_; lean_object* v_messages_2959_; lean_object* v_infoState_2960_; lean_object* v_snapshotTasks_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2973_; 
v_toCold_2950_ = lean_ctor_get(v___y_2947_, 0);
v_currNamespace_2951_ = lean_ctor_get(v_toCold_2950_, 4);
v___x_2952_ = lean_st_ref_take(v___y_2948_);
v_env_2953_ = lean_ctor_get(v___x_2952_, 0);
v_nextMacroScope_2954_ = lean_ctor_get(v___x_2952_, 1);
v_ngen_2955_ = lean_ctor_get(v___x_2952_, 2);
v_auxDeclNGen_2956_ = lean_ctor_get(v___x_2952_, 3);
v_traceState_2957_ = lean_ctor_get(v___x_2952_, 4);
v_recordedDeps_2958_ = lean_ctor_get(v___x_2952_, 6);
v_messages_2959_ = lean_ctor_get(v___x_2952_, 7);
v_infoState_2960_ = lean_ctor_get(v___x_2952_, 8);
v_snapshotTasks_2961_ = lean_ctor_get(v___x_2952_, 9);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v___x_2952_, 5);
lean_dec(v_unused_2974_);
v___x_2963_ = v___x_2952_;
v_isShared_2964_ = v_isSharedCheck_2973_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snapshotTasks_2961_);
lean_inc(v_infoState_2960_);
lean_inc(v_messages_2959_);
lean_inc(v_recordedDeps_2958_);
lean_inc(v_traceState_2957_);
lean_inc(v_auxDeclNGen_2956_);
lean_inc(v_ngen_2955_);
lean_inc(v_nextMacroScope_2954_);
lean_inc(v_env_2953_);
lean_dec(v___x_2952_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2973_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2965_ = lean_box(0);
lean_inc(v_currNamespace_2951_);
v___x_2966_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2953_, v_ext_2944_, v_b_2945_, v_kind_2946_, v_currNamespace_2951_);
v___x_2967_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 5, v___x_2967_);
lean_ctor_set(v___x_2963_, 0, v___x_2966_);
v___x_2969_ = v___x_2963_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_nextMacroScope_2954_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v_ngen_2955_);
lean_ctor_set(v_reuseFailAlloc_2972_, 3, v_auxDeclNGen_2956_);
lean_ctor_set(v_reuseFailAlloc_2972_, 4, v_traceState_2957_);
lean_ctor_set(v_reuseFailAlloc_2972_, 5, v___x_2967_);
lean_ctor_set(v_reuseFailAlloc_2972_, 6, v_recordedDeps_2958_);
lean_ctor_set(v_reuseFailAlloc_2972_, 7, v_messages_2959_);
lean_ctor_set(v_reuseFailAlloc_2972_, 8, v_infoState_2960_);
lean_ctor_set(v_reuseFailAlloc_2972_, 9, v_snapshotTasks_2961_);
v___x_2969_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_st_ref_put(v___y_2948_, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2965_);
return v___x_2971_;
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2944_ = stack[0].m_obj;
lean_object* v_b_2945_ = stack[1].m_obj;
uint8_t v_kind_2946_ = stack[2].m_num;
lean_object* v___y_2947_ = stack[3].m_obj;
lean_object* v___y_2948_ = stack[4].m_obj;
lean_object* v_res_2975_;
v_res_2975_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2944_, v_b_2945_, v_kind_2946_, v___y_2947_, v___y_2948_);
stack->m_obj
 = v_res_2975_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object* v_ext_2976_, lean_object* v_b_2977_, lean_object* v_kind_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
uint8_t v_kind_boxed_2982_; lean_object* v_res_2983_; 
v_kind_boxed_2982_ = lean_unbox(v_kind_2978_);
v_res_2983_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2976_, v_b_2977_, v_kind_boxed_2982_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
return v_res_2983_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object* v_00_u03b1_2984_, lean_object* v_00_u03b2_2985_, lean_object* v_00_u03c3_2986_, lean_object* v_ext_2987_, lean_object* v_b_2988_, uint8_t v_kind_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2987_, v_b_2988_, v_kind_2989_, v___y_2990_, v___y_2991_);
return v___x_2993_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_2987_ = stack[3].m_obj;
lean_object* v_b_2988_ = stack[4].m_obj;
uint8_t v_kind_2989_ = stack[5].m_num;
lean_object* v___y_2990_ = stack[6].m_obj;
lean_object* v___y_2991_ = stack[7].m_obj;
lean_object* v_res_2994_;
v_res_2994_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_box(0), lean_box(0), lean_box(0), v_ext_2987_, v_b_2988_, v_kind_2989_, v___y_2990_, v___y_2991_);
stack->m_obj
 = v_res_2994_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object* v_00_u03b1_2995_, lean_object* v_00_u03b2_2996_, lean_object* v_00_u03c3_2997_, lean_object* v_ext_2998_, lean_object* v_b_2999_, lean_object* v_kind_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v_kind_boxed_3004_; lean_object* v_res_3005_; 
v_kind_boxed_3004_ = lean_unbox(v_kind_3000_);
v_res_3005_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(v_00_u03b1_2995_, v_00_u03b2_2996_, v_00_u03c3_2997_, v_ext_2998_, v_b_2999_, v_kind_boxed_3004_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3005_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0));
v___x_3008_ = l_Lean_stringToMessageData(v___x_3007_);
return v___x_3008_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2));
v___x_3011_ = l_Lean_stringToMessageData(v___x_3010_);
return v___x_3011_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object* v_declName_3012_, uint8_t v_kind_3013_, uint8_t v_phase_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v___x_3018_; lean_object* v_env_3019_; lean_object* v_ref_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3018_ = lean_st_ref_get(v_a_3016_);
v_env_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc_ref(v_env_3019_);
lean_dec(v___x_3018_);
v_ref_3020_ = lean_ctor_get(v_a_3015_, 2);
v___x_3021_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3015_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_env_3019_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
lean_inc(v_declName_3012_);
v___x_3023_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_3012_, v___x_3022_);
lean_dec_ref_known(v___x_3022_, 2);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; lean_object* v_a_3026_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
lean_inc(v_declName_3012_);
v___x_3025_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_3012_, v_a_3016_);
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
if (lean_obj_tag(v_a_3026_) == 1)
{
lean_object* v_val_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_val_3027_ = lean_ctor_get(v_a_3026_, 0);
lean_inc(v_val_3027_);
lean_dec_ref_known(v_a_3026_, 1);
v___x_3028_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v___x_3029_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3029_, 0, v_declName_3012_);
lean_ctor_set(v___x_3029_, 1, v_val_3027_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*2, v_phase_3014_);
v___x_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v_a_3024_);
v___x_3031_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v___x_3028_, v___x_3030_, v_kind_3013_, v_a_3015_, v_a_3016_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec(v_a_3026_);
lean_dec(v_a_3024_);
v___x_3032_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1);
v___x_3033_ = 0;
v___x_3034_ = l_Lean_MessageData_ofConstName(v_declName_3012_, v___x_3033_);
v___x_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3032_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_3037_, v_a_3015_, v_a_3016_);
return v___x_3038_;
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_declName_3012_);
v_a_3039_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3041_ = v___x_3023_;
v_isShared_3042_ = v_isSharedCheck_3050_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3023_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3050_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3043_ = lean_io_error_to_string(v_a_3039_);
v___x_3044_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
v___x_3045_ = l_Lean_MessageData_ofFormat(v___x_3044_);
lean_inc(v_ref_3020_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v_ref_3020_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3046_);
v___x_3048_ = v___x_3041_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3012_ = stack[0].m_obj;
uint8_t v_kind_3013_ = stack[1].m_num;
uint8_t v_phase_3014_ = stack[2].m_num;
lean_object* v_a_3015_ = stack[3].m_obj;
lean_object* v_a_3016_ = stack[4].m_obj;
lean_object* v_res_3051_;
v_res_3051_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_3012_, v_kind_3013_, v_phase_3014_, v_a_3015_, v_a_3016_);
stack->m_obj
 = v_res_3051_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object* v_declName_3052_, lean_object* v_kind_3053_, lean_object* v_phase_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
uint8_t v_kind_boxed_3058_; uint8_t v_phase_boxed_3059_; lean_object* v_res_3060_; 
v_kind_boxed_3058_ = lean_unbox(v_kind_3053_);
v_phase_boxed_3059_ = lean_unbox(v_phase_3054_);
v_res_3060_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_3052_, v_kind_boxed_3058_, v_phase_boxed_3059_, v_a_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
return v_res_3060_;
}
}
uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object* v_stx_3073_){
_start:
{
uint8_t v___x_3074_; 
v___x_3074_ = l_Lean_Syntax_isNone(v_stx_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v_inner_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3075_ = lean_unsigned_to_nat(0u);
v_inner_3076_ = l_Lean_Syntax_getArg(v_stx_3073_, v___x_3075_);
v___x_3077_ = l_Lean_Syntax_getKind(v_inner_3076_);
v___x_3078_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2));
v___x_3079_ = lean_name_eq(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4));
v___x_3081_ = lean_name_eq(v___x_3077_, v___x_3080_);
lean_dec(v___x_3077_);
if (v___x_3081_ == 0)
{
uint8_t v___x_3082_; 
v___x_3082_ = 2;
return v___x_3082_;
}
else
{
uint8_t v___x_3083_; 
v___x_3083_ = 1;
return v___x_3083_;
}
}
else
{
uint8_t v___x_3084_; 
lean_dec(v___x_3077_);
v___x_3084_ = 0;
return v___x_3084_;
}
}
else
{
uint8_t v___x_3085_; 
v___x_3085_ = 2;
return v___x_3085_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3073_ = stack[0].m_obj;
uint8_t v_res_3086_;
v_res_3086_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_3073_);
stack->m_num = v_res_3086_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object* v_stx_3087_){
_start:
{
uint8_t v_res_3088_; lean_object* v_r_3089_; 
v_res_3088_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_3087_);
lean_dec(v_stx_3087_);
v_r_3089_ = lean_box(v_res_3088_);
return v_r_3089_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_3094_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
lean_ctor_set(v___x_3094_, 2, v___x_3093_);
lean_ctor_set(v___x_3094_, 3, v___x_3093_);
lean_ctor_set(v___x_3094_, 4, v___x_3093_);
lean_ctor_set(v___x_3094_, 5, v___x_3093_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_unsigned_to_nat(32u);
v___x_3096_ = lean_mk_empty_array_with_capacity(v___x_3095_);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4(void){
_start:
{
size_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3098_ = ((size_t)5ULL);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_unsigned_to_nat(32u);
v___x_3101_ = lean_mk_empty_array_with_capacity(v___x_3100_);
v___x_3102_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3);
v___x_3103_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___x_3101_);
lean_ctor_set(v___x_3103_, 2, v___x_3099_);
lean_ctor_set(v___x_3103_, 3, v___x_3099_);
lean_ctor_set_usize(v___x_3103_, 4, v___x_3098_);
return v___x_3103_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_3105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
lean_ctor_set(v___x_3105_, 2, v___x_3104_);
lean_ctor_set(v___x_3105_, 3, v___x_3104_);
lean_ctor_set(v___x_3105_, 4, v___x_3104_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3106_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5);
v___x_3107_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4);
v___x_3108_ = lean_box(1);
v___x_3109_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2);
v___x_3110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_3111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v___x_3109_);
lean_ctor_set(v___x_3111_, 2, v___x_3108_);
lean_ctor_set(v___x_3111_, 3, v___x_3107_);
lean_ctor_set(v___x_3111_, 4, v___x_3106_);
return v___x_3111_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object* v_declName_3112_, lean_object* v_stx_3113_, uint8_t v_attrKind_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1));
lean_inc(v_declName_3112_);
v___x_3119_ = l_Lean_ensureAttrDeclIsMeta(v___x_3118_, v_declName_3112_, v_attrKind_3114_, v_a_3115_, v_a_3116_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref_known(v___x_3119_, 1);
v___x_3120_ = lean_unsigned_to_nat(1u);
v___x_3121_ = l_Lean_Syntax_getArg(v_stx_3113_, v___x_3120_);
v___x_3122_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_3121_);
lean_dec(v___x_3121_);
v___x_3123_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_3124_ = lean_box(0);
v___x_3125_ = lean_st_mk_ref(v___x_3123_);
v___x_3126_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_3112_, v_attrKind_3114_, v___x_3122_, v_a_3115_, v_a_3116_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3134_; 
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_3126_, 0);
lean_dec(v_unused_3135_);
v___x_3128_ = v___x_3126_;
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
else
{
lean_dec(v___x_3126_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = lean_st_ref_get(v___x_3125_);
lean_dec(v___x_3125_);
lean_dec(v___x_3130_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3124_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3124_);
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
lean_dec(v___x_3125_);
return v___x_3126_;
}
}
else
{
lean_dec(v_declName_3112_);
return v___x_3119_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3112_ = stack[0].m_obj;
lean_object* v_stx_3113_ = stack[1].m_obj;
uint8_t v_attrKind_3114_ = stack[2].m_num;
lean_object* v_a_3115_ = stack[3].m_obj;
lean_object* v_a_3116_ = stack[4].m_obj;
lean_object* v_res_3136_;
v_res_3136_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(v_declName_3112_, v_stx_3113_, v_attrKind_3114_, v_a_3115_, v_a_3116_);
stack->m_obj
 = v_res_3136_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object* v_declName_3137_, lean_object* v_stx_3138_, lean_object* v_attrKind_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
uint8_t v_attrKind_boxed_3143_; lean_object* v_res_3144_; 
v_attrKind_boxed_3143_ = lean_unbox(v_attrKind_3139_);
v_res_3144_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(v_declName_3137_, v_stx_3138_, v_attrKind_boxed_3143_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_stx_3138_);
return v_res_3144_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object* v_ref_3147_, lean_object* v_declName_3148_, uint8_t v_phase_3149_, lean_object* v_proc_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_keys_3154_; lean_object* v___x_3155_; 
v___x_3152_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_3153_ = lean_st_ref_get(v___x_3152_);
v_keys_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc_ref(v_keys_3154_);
lean_dec(v___x_3153_);
v___x_3155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_keys_3154_, v_declName_3148_);
lean_dec_ref(v_keys_3154_);
if (lean_obj_tag(v___x_3155_) == 1)
{
lean_object* v_val_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3166_; 
v_val_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3166_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_val_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3166_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3160_ = lean_st_ref_take(v_ref_3147_);
v___x_3161_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v___x_3160_, v_val_3156_, v_declName_3148_, v_phase_3149_, v_proc_3150_);
v___x_3162_ = lean_st_ref_put(v_ref_3147_, v___x_3161_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3162_);
v___x_3164_ = v___x_3158_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_dec(v___x_3155_);
lean_dec_ref(v_proc_3150_);
v___x_3167_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0));
v___x_3168_ = l_Lean_privateToUserName(v_declName_3148_);
v___x_3169_ = 1;
v___x_3170_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3168_, v___x_3169_);
v___x_3171_ = lean_string_append(v___x_3167_, v___x_3170_);
lean_dec_ref(v___x_3170_);
v___x_3172_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1));
v___x_3173_ = lean_string_append(v___x_3171_, v___x_3172_);
v___x_3174_ = lean_mk_io_user_error(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3147_ = stack[0].m_obj;
lean_object* v_declName_3148_ = stack[1].m_obj;
uint8_t v_phase_3149_ = stack[2].m_num;
lean_object* v_proc_3150_ = stack[3].m_obj;
lean_object* v_res_3176_;
v_res_3176_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v_ref_3147_, v_declName_3148_, v_phase_3149_, v_proc_3150_);
stack->m_obj
 = v_res_3176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object* v_ref_3177_, lean_object* v_declName_3178_, lean_object* v_phase_3179_, lean_object* v_proc_3180_, lean_object* v_a_3181_){
_start:
{
uint8_t v_phase_boxed_3182_; lean_object* v_res_3183_; 
v_phase_boxed_3182_ = lean_unbox(v_phase_3179_);
v_res_3183_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v_ref_3177_, v_declName_3178_, v_phase_boxed_3182_, v_proc_3180_);
lean_dec(v_ref_3177_);
return v_res_3183_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object* v_declName_3184_, uint8_t v_phase_3185_, lean_object* v_proc_3186_){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___x_3189_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v___x_3188_, v_declName_3184_, v_phase_3185_, v_proc_3186_);
return v___x_3189_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3184_ = stack[0].m_obj;
uint8_t v_phase_3185_ = stack[1].m_num;
lean_object* v_proc_3186_ = stack[2].m_obj;
lean_object* v_res_3190_;
v_res_3190_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v_declName_3184_, v_phase_3185_, v_proc_3186_);
stack->m_obj
 = v_res_3190_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object* v_declName_3191_, lean_object* v_phase_3192_, lean_object* v_proc_3193_, lean_object* v_a_3194_){
_start:
{
uint8_t v_phase_boxed_3195_; lean_object* v_res_3196_; 
v_phase_boxed_3195_ = lean_unbox(v_phase_3192_);
v_res_3196_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v_declName_3191_, v_phase_boxed_3195_, v_proc_3193_);
return v_res_3196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_box(0);
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1));
v___x_3206_ = l_Lean_mkConst(v___x_3205_, v___x_3204_);
return v___x_3206_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object* v_declName_3210_, lean_object* v_stx_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v_phase_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___y_3222_; 
v___x_3215_ = lean_unsigned_to_nat(1u);
v___x_3216_ = l_Lean_Syntax_getArg(v_stx_3211_, v___x_3215_);
v_phase_3217_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_3216_);
lean_dec(v___x_3216_);
v___x_3218_ = lean_box(0);
v___x_3219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2);
lean_inc(v_declName_3210_);
v___x_3220_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_3210_);
switch(v_phase_3217_)
{
case 0:
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
v___y_3222_ = v___x_3254_;
goto v___jp_3221_;
}
case 1:
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
v___y_3222_ = v___x_3255_;
goto v___jp_3221_;
}
default: 
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
v___y_3222_ = v___x_3256_;
goto v___jp_3221_;
}
}
v___jp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v_val_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_inc(v_declName_3210_);
v___x_3223_ = l_Lean_mkConst(v_declName_3210_, v___x_3218_);
v___x_3224_ = lean_unsigned_to_nat(3u);
v___x_3225_ = lean_mk_empty_array_with_capacity(v___x_3224_);
v___x_3226_ = lean_array_push(v___x_3225_, v___x_3220_);
lean_inc_ref(v___y_3222_);
v___x_3227_ = lean_array_push(v___x_3226_, v___y_3222_);
v___x_3228_ = lean_array_push(v___x_3227_, v___x_3223_);
v_val_3229_ = l_Lean_mkAppN(v___x_3219_, v___x_3228_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4));
v___x_3231_ = l_Lean_Name_append(v_declName_3210_, v___x_3230_);
v___x_3232_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_3233_ = lean_st_mk_ref(v___x_3232_);
v___x_3234_ = l_Lean_Core_mkFreshUserName(v___x_3231_, v_a_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3236_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v___x_3236_ = l_Lean_declareBuiltin(v_a_3235_, v_val_3229_, v_a_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3245_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3245_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3245_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3241_ = lean_st_ref_get(v___x_3233_);
lean_dec(v___x_3233_);
lean_dec(v___x_3241_);
if (v_isShared_3240_ == 0)
{
v___x_3243_ = v___x_3239_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3237_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
else
{
lean_dec(v___x_3233_);
return v___x_3236_;
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v___x_3233_);
lean_dec_ref(v_val_3229_);
v_a_3246_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3234_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3234_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3210_ = stack[0].m_obj;
lean_object* v_stx_3211_ = stack[1].m_obj;
lean_object* v_a_3212_ = stack[2].m_obj;
lean_object* v_a_3213_ = stack[3].m_obj;
lean_object* v_res_3257_;
v_res_3257_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3210_, v_stx_3211_, v_a_3212_, v_a_3213_);
stack->m_obj
 = v_res_3257_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object* v_declName_3258_, lean_object* v_stx_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3258_, v_stx_3259_, v_a_3260_, v_a_3261_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_stx_3259_);
return v_res_3263_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3350_ = l_Lean_registerBuiltinAttribute(v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3351_;
v_res_3351_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object* v_a_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
return v_res_3353_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_declName_3354_, lean_object* v_stx_3355_, uint8_t v_x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; 
v___x_3360_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3354_, v_stx_3355_, v___y_3357_, v___y_3358_);
return v___x_3360_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3354_ = stack[0].m_obj;
lean_object* v_stx_3355_ = stack[1].m_obj;
uint8_t v_x_3356_ = stack[2].m_num;
lean_object* v___y_3357_ = stack[3].m_obj;
lean_object* v___y_3358_ = stack[4].m_obj;
lean_object* v_res_3361_;
v_res_3361_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_3354_, v_stx_3355_, v_x_3356_, v___y_3357_, v___y_3358_);
stack->m_obj
 = v_res_3361_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_declName_3362_, lean_object* v_stx_3363_, lean_object* v_x_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
uint8_t v_x_117__boxed_3368_; lean_object* v_res_3369_; 
v_x_117__boxed_3368_ = lean_unbox(v_x_3364_);
v_res_3369_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_3362_, v_stx_3363_, v_x_117__boxed_3368_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v_stx_3363_);
return v_res_3369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3372_ = l_Lean_stringToMessageData(v___x_3371_);
return v___x_3372_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3378_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_3377_, v___y_3374_, v___y_3375_);
return v___x_3378_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3373_ = stack[0].m_obj;
lean_object* v___y_3374_ = stack[1].m_obj;
lean_object* v___y_3375_ = stack[2].m_obj;
lean_object* v_res_3379_;
v_res_3379_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_3373_, v___y_3374_, v___y_3375_);
stack->m_obj
 = v_res_3379_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_x_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v_x_3380_);
return v_res_3384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_unsigned_to_nat(3124561870u);
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3389_ = l_Lean_Name_num___override(v___x_3388_, v___x_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3392_ = l_Lean_Name_str___override(v___x_3391_, v___x_3390_);
return v___x_3392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3395_ = l_Lean_Name_str___override(v___x_3394_, v___x_3393_);
return v___x_3395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = lean_unsigned_to_nat(2u);
v___x_3397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3398_ = l_Lean_Name_num___override(v___x_3397_, v___x_3396_);
return v___x_3398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3403_ = 1;
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3407_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v___x_3405_);
lean_ctor_set(v___x_3407_, 2, v___x_3404_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*3, v___x_3403_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3408_; lean_object* v___f_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___f_3408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___f_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v___f_3409_);
lean_ctor_set(v___x_3411_, 2, v___f_3408_);
return v___x_3411_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3414_ = l_Lean_registerBuiltinAttribute(v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3415_;
v_res_3415_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3415_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_a_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
return v_res_3417_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object* v_a_3418_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v_env_3422_; lean_object* v___x_3423_; lean_object* v_ext_3424_; lean_object* v_toEnvExtension_3425_; lean_object* v_asyncMode_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3420_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_3421_ = lean_st_ref_get(v_a_3418_);
v_env_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc_ref(v_env_3422_);
lean_dec(v___x_3421_);
v___x_3423_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_3424_ = lean_ctor_get(v___x_3423_, 1);
v_toEnvExtension_3425_ = lean_ctor_get(v_ext_3424_, 0);
v_asyncMode_3426_ = lean_ctor_get(v_toEnvExtension_3425_, 2);
v___x_3427_ = 0;
v___x_3428_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3420_, v___x_3423_, v_env_3422_, v_asyncMode_3426_, v___x_3427_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3418_ = stack[0].m_obj;
lean_object* v_res_3430_;
v_res_3430_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3418_);
stack->m_obj
 = v_res_3430_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3431_);
lean_dec(v_a_3431_);
return v_res_3433_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3435_);
return v___x_3437_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_getCbvSimprocs_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3434_ = stack[0].m_obj;
lean_object* v_a_3435_ = stack[1].m_obj;
lean_object* v_res_3438_;
v_res_3438_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_3434_, v_a_3435_);
stack->m_obj
 = v_res_3438_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_3439_, v_a_3440_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
return v_res_3442_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = lean_unsigned_to_nat(32u);
v___x_3444_ = lean_mk_empty_array_with_capacity(v___x_3443_);
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3446_ = ((size_t)5ULL);
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = lean_unsigned_to_nat(32u);
v___x_3449_ = lean_mk_empty_array_with_capacity(v___x_3448_);
v___x_3450_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0);
v___x_3451_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v___x_3449_);
lean_ctor_set(v___x_3451_, 2, v___x_3447_);
lean_ctor_set(v___x_3451_, 3, v___x_3447_);
lean_ctor_set_usize(v___x_3451_, 4, v___x_3446_);
return v___x_3451_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; lean_object* v_traceState_3455_; lean_object* v_traces_3456_; lean_object* v___x_3457_; lean_object* v_traceState_3458_; lean_object* v_env_3459_; lean_object* v_nextMacroScope_3460_; lean_object* v_ngen_3461_; lean_object* v_auxDeclNGen_3462_; lean_object* v_cache_3463_; lean_object* v_recordedDeps_3464_; lean_object* v_messages_3465_; lean_object* v_infoState_3466_; lean_object* v_snapshotTasks_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3486_; 
v___x_3454_ = lean_st_ref_get(v___y_3452_);
v_traceState_3455_ = lean_ctor_get(v___x_3454_, 4);
lean_inc_ref(v_traceState_3455_);
lean_dec(v___x_3454_);
v_traces_3456_ = lean_ctor_get(v_traceState_3455_, 0);
lean_inc_ref(v_traces_3456_);
lean_dec_ref(v_traceState_3455_);
v___x_3457_ = lean_st_ref_take(v___y_3452_);
v_traceState_3458_ = lean_ctor_get(v___x_3457_, 4);
v_env_3459_ = lean_ctor_get(v___x_3457_, 0);
v_nextMacroScope_3460_ = lean_ctor_get(v___x_3457_, 1);
v_ngen_3461_ = lean_ctor_get(v___x_3457_, 2);
v_auxDeclNGen_3462_ = lean_ctor_get(v___x_3457_, 3);
v_cache_3463_ = lean_ctor_get(v___x_3457_, 5);
v_recordedDeps_3464_ = lean_ctor_get(v___x_3457_, 6);
v_messages_3465_ = lean_ctor_get(v___x_3457_, 7);
v_infoState_3466_ = lean_ctor_get(v___x_3457_, 8);
v_snapshotTasks_3467_ = lean_ctor_get(v___x_3457_, 9);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3469_ = v___x_3457_;
v_isShared_3470_ = v_isSharedCheck_3486_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_snapshotTasks_3467_);
lean_inc(v_infoState_3466_);
lean_inc(v_messages_3465_);
lean_inc(v_recordedDeps_3464_);
lean_inc(v_cache_3463_);
lean_inc(v_traceState_3458_);
lean_inc(v_auxDeclNGen_3462_);
lean_inc(v_ngen_3461_);
lean_inc(v_nextMacroScope_3460_);
lean_inc(v_env_3459_);
lean_dec(v___x_3457_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3486_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
uint64_t v_tid_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3484_; 
v_tid_3471_ = lean_ctor_get_uint64(v_traceState_3458_, sizeof(void*)*1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_traceState_3458_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v_traceState_3458_, 0);
lean_dec(v_unused_3485_);
v___x_3473_ = v_traceState_3458_;
v_isShared_3474_ = v_isSharedCheck_3484_;
goto v_resetjp_3472_;
}
else
{
lean_dec(v_traceState_3458_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3484_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3475_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1);
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v___x_3475_);
v___x_3477_ = v___x_3473_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3475_);
lean_ctor_set_uint64(v_reuseFailAlloc_3483_, sizeof(void*)*1, v_tid_3471_);
v___x_3477_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 4, v___x_3477_);
v___x_3479_ = v___x_3469_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_env_3459_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_nextMacroScope_3460_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_ngen_3461_);
lean_ctor_set(v_reuseFailAlloc_3482_, 3, v_auxDeclNGen_3462_);
lean_ctor_set(v_reuseFailAlloc_3482_, 4, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3482_, 5, v_cache_3463_);
lean_ctor_set(v_reuseFailAlloc_3482_, 6, v_recordedDeps_3464_);
lean_ctor_set(v_reuseFailAlloc_3482_, 7, v_messages_3465_);
lean_ctor_set(v_reuseFailAlloc_3482_, 8, v_infoState_3466_);
lean_ctor_set(v_reuseFailAlloc_3482_, 9, v_snapshotTasks_3467_);
v___x_3479_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_st_ref_put(v___y_3452_, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_traces_3456_);
return v___x_3481_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3452_ = stack[0].m_obj;
lean_object* v_res_3487_;
v_res_3487_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3452_);
stack->m_obj
 = v_res_3487_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3488_);
lean_dec(v___y_3488_);
return v_res_3490_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3491_ = stack[0].m_obj;
lean_object* v___y_3492_ = stack[1].m_obj;
lean_object* v___y_3493_ = stack[2].m_obj;
lean_object* v___y_3494_ = stack[3].m_obj;
lean_object* v___y_3495_ = stack[4].m_obj;
lean_object* v___y_3496_ = stack[5].m_obj;
lean_object* v___y_3497_ = stack[6].m_obj;
lean_object* v___y_3498_ = stack[7].m_obj;
lean_object* v___y_3499_ = stack[8].m_obj;
lean_object* v_res_3502_;
v_res_3502_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
stack->m_obj
 = v_res_3502_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
return v_res_3513_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object* v_opts_3514_, lean_object* v_opt_3515_){
_start:
{
lean_object* v_name_3516_; lean_object* v_defValue_3517_; lean_object* v_map_3518_; lean_object* v___x_3519_; 
v_name_3516_ = lean_ctor_get(v_opt_3515_, 0);
v_defValue_3517_ = lean_ctor_get(v_opt_3515_, 1);
v_map_3518_ = lean_ctor_get(v_opts_3514_, 0);
v___x_3519_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3518_, v_name_3516_);
if (lean_obj_tag(v___x_3519_) == 0)
{
uint8_t v___x_3520_; 
v___x_3520_ = lean_unbox(v_defValue_3517_);
return v___x_3520_;
}
else
{
lean_object* v_val_3521_; 
v_val_3521_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_val_3521_);
lean_dec_ref_known(v___x_3519_, 1);
if (lean_obj_tag(v_val_3521_) == 1)
{
uint8_t v_v_3522_; 
v_v_3522_ = lean_ctor_get_uint8(v_val_3521_, 0);
lean_dec_ref_known(v_val_3521_, 0);
return v_v_3522_;
}
else
{
uint8_t v___x_3523_; 
lean_dec(v_val_3521_);
v___x_3523_ = lean_unbox(v_defValue_3517_);
return v___x_3523_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_3514_ = stack[0].m_obj;
lean_object* v_opt_3515_ = stack[1].m_obj;
uint8_t v_res_3524_;
v_res_3524_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3514_, v_opt_3515_);
stack->m_num = v_res_3524_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object* v_opts_3525_, lean_object* v_opt_3526_){
_start:
{
uint8_t v_res_3527_; lean_object* v_r_3528_; 
v_res_3527_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3525_, v_opt_3526_);
lean_dec_ref(v_opt_3526_);
lean_dec_ref(v_opts_3525_);
v_r_3528_ = lean_box(v_res_3527_);
return v_r_3528_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(uint8_t v___x_3529_, lean_object* v_e_3530_, lean_object* v_snd_3531_, lean_object* v_proc_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
if (v___x_3529_ == 0)
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_3530_, v_snd_3531_, v_proc_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; 
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3538_);
lean_inc(v___y_3537_);
lean_inc_ref(v___y_3536_);
lean_inc(v___y_3535_);
lean_inc_ref(v___y_3534_);
lean_inc(v___y_3533_);
v___x_3544_ = lean_apply_11(v_proc_3532_, v_e_3530_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, lean_box(0));
return v___x_3544_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3529_ = stack[0].m_num;
lean_object* v_e_3530_ = stack[1].m_obj;
lean_object* v_snd_3531_ = stack[2].m_obj;
lean_object* v_proc_3532_ = stack[3].m_obj;
lean_object* v___y_3533_ = stack[4].m_obj;
lean_object* v___y_3534_ = stack[5].m_obj;
lean_object* v___y_3535_ = stack[6].m_obj;
lean_object* v___y_3536_ = stack[7].m_obj;
lean_object* v___y_3537_ = stack[8].m_obj;
lean_object* v___y_3538_ = stack[9].m_obj;
lean_object* v___y_3539_ = stack[10].m_obj;
lean_object* v___y_3540_ = stack[11].m_obj;
lean_object* v___y_3541_ = stack[12].m_obj;
lean_object* v_res_3545_;
v_res_3545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_3529_, v_e_3530_, v_snd_3531_, v_proc_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
stack->m_obj
 = v_res_3545_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(lean_object* v___x_3546_, lean_object* v_e_3547_, lean_object* v_snd_3548_, lean_object* v_proc_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
uint8_t v___x_52003__boxed_3560_; lean_object* v_res_3561_; 
v___x_52003__boxed_3560_ = lean_unbox(v___x_3546_);
v_res_3561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_52003__boxed_3560_, v_e_3547_, v_snd_3548_, v_proc_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec(v_snd_3548_);
return v_res_3561_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(lean_object* v_x_3562_){
_start:
{
if (lean_obj_tag(v_x_3562_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
v_a_3564_ = lean_ctor_get(v_x_3562_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v_x_3562_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v_x_3562_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set_tag(v___x_3566_, 1);
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
v_a_3572_ = lean_ctor_get(v_x_3562_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v_x_3562_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v_x_3562_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 0);
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3562_ = stack[0].m_obj;
lean_object* v_res_3580_;
v_res_3580_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_3562_);
stack->m_obj
 = v_res_3580_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(lean_object* v_x_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_3581_);
return v_res_3583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(size_t v_sz_3584_, size_t v_i_3585_, lean_object* v_bs_3586_){
_start:
{
uint8_t v___x_3587_; 
v___x_3587_ = lean_usize_dec_lt(v_i_3585_, v_sz_3584_);
if (v___x_3587_ == 0)
{
return v_bs_3586_;
}
else
{
lean_object* v_v_3588_; lean_object* v_msg_3589_; lean_object* v___x_3590_; lean_object* v_bs_x27_3591_; size_t v___x_3592_; size_t v___x_3593_; lean_object* v___x_3594_; 
v_v_3588_ = lean_array_uget_borrowed(v_bs_3586_, v_i_3585_);
v_msg_3589_ = lean_ctor_get(v_v_3588_, 1);
lean_inc_ref(v_msg_3589_);
v___x_3590_ = lean_unsigned_to_nat(0u);
v_bs_x27_3591_ = lean_array_uset(v_bs_3586_, v_i_3585_, v___x_3590_);
v___x_3592_ = ((size_t)1ULL);
v___x_3593_ = lean_usize_add(v_i_3585_, v___x_3592_);
v___x_3594_ = lean_array_uset(v_bs_x27_3591_, v_i_3585_, v_msg_3589_);
v_i_3585_ = v___x_3593_;
v_bs_3586_ = v___x_3594_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3584_ = stack[0].m_num;
size_t v_i_3585_ = stack[1].m_num;
lean_object* v_bs_3586_ = stack[2].m_obj;
lean_object* v_res_3596_;
v_res_3596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_3584_, v_i_3585_, v_bs_3586_);
stack->m_obj
 = v_res_3596_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_3597_, lean_object* v_i_3598_, lean_object* v_bs_3599_){
_start:
{
size_t v_sz_boxed_3600_; size_t v_i_boxed_3601_; lean_object* v_res_3602_; 
v_sz_boxed_3600_ = lean_unbox_usize(v_sz_3597_);
lean_dec(v_sz_3597_);
v_i_boxed_3601_ = lean_unbox_usize(v_i_3598_);
lean_dec(v_i_3598_);
v_res_3602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_boxed_3600_, v_i_boxed_3601_, v_bs_3599_);
return v_res_3602_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(lean_object* v_msgData_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v_env_3610_; uint8_t v___x_3611_; lean_object* v_env_3612_; lean_object* v___x_3613_; lean_object* v_toCold_3614_; lean_object* v_mctx_3615_; lean_object* v_lctx_3616_; lean_object* v_options_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3609_ = lean_st_ref_get(v___y_3607_);
v_env_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc_ref(v_env_3610_);
lean_dec(v___x_3609_);
v___x_3611_ = 0;
v_env_3612_ = l_Lean_Environment_setRecordingDeps(v_env_3610_, v___x_3611_);
v___x_3613_ = lean_st_ref_get(v___y_3605_);
v_toCold_3614_ = lean_ctor_get(v___y_3606_, 0);
v_mctx_3615_ = lean_ctor_get(v___x_3613_, 0);
lean_inc_ref(v_mctx_3615_);
lean_dec(v___x_3613_);
v_lctx_3616_ = lean_ctor_get(v___y_3604_, 2);
v_options_3617_ = lean_ctor_get(v_toCold_3614_, 2);
lean_inc_ref(v_options_3617_);
lean_inc_ref(v_lctx_3616_);
v___x_3618_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3618_, 0, v_env_3612_);
lean_ctor_set(v___x_3618_, 1, v_mctx_3615_);
lean_ctor_set(v___x_3618_, 2, v_lctx_3616_);
lean_ctor_set(v___x_3618_, 3, v_options_3617_);
v___x_3619_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
lean_ctor_set(v___x_3619_, 1, v_msgData_3603_);
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3603_ = stack[0].m_obj;
lean_object* v___y_3604_ = stack[1].m_obj;
lean_object* v___y_3605_ = stack[2].m_obj;
lean_object* v___y_3606_ = stack[3].m_obj;
lean_object* v___y_3607_ = stack[4].m_obj;
lean_object* v_res_3621_;
v_res_3621_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msgData_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
stack->m_obj
 = v_res_3621_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4___boxed(lean_object* v_msgData_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msgData_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
return v_res_3628_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(lean_object* v_oldTraces_3629_, lean_object* v_data_3630_, lean_object* v_ref_3631_, lean_object* v_msg_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_toCold_3638_; lean_object* v_currRecDepth_3639_; lean_object* v_ref_3640_; uint16_t v_optionFlags_3641_; uint8_t v_suppressElabErrors_3642_; uint8_t v_isRecordingDeps_3643_; lean_object* v_ref_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_traceState_3647_; lean_object* v_traces_3648_; lean_object* v___x_3649_; size_t v_sz_3650_; size_t v___x_3651_; lean_object* v___x_3652_; lean_object* v_msg_3653_; lean_object* v___x_3654_; lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3693_; 
v_toCold_3638_ = lean_ctor_get(v___y_3635_, 0);
v_currRecDepth_3639_ = lean_ctor_get(v___y_3635_, 1);
v_ref_3640_ = lean_ctor_get(v___y_3635_, 2);
v_optionFlags_3641_ = lean_ctor_get_uint16(v___y_3635_, sizeof(void*)*3);
v_suppressElabErrors_3642_ = lean_ctor_get_uint8(v___y_3635_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3643_ = lean_ctor_get_uint8(v___y_3635_, sizeof(void*)*3 + 3);
v_ref_3644_ = l_Lean_replaceRef(v_ref_3631_, v_ref_3640_);
lean_inc(v_currRecDepth_3639_);
lean_inc_ref(v_toCold_3638_);
v___x_3645_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3645_, 0, v_toCold_3638_);
lean_ctor_set(v___x_3645_, 1, v_currRecDepth_3639_);
lean_ctor_set(v___x_3645_, 2, v_ref_3644_);
lean_ctor_set_uint16(v___x_3645_, sizeof(void*)*3, v_optionFlags_3641_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*3 + 2, v_suppressElabErrors_3642_);
lean_ctor_set_uint8(v___x_3645_, sizeof(void*)*3 + 3, v_isRecordingDeps_3643_);
v___x_3646_ = lean_st_ref_get(v___y_3636_);
v_traceState_3647_ = lean_ctor_get(v___x_3646_, 4);
lean_inc_ref(v_traceState_3647_);
lean_dec(v___x_3646_);
v_traces_3648_ = lean_ctor_get(v_traceState_3647_, 0);
lean_inc_ref(v_traces_3648_);
lean_dec_ref(v_traceState_3647_);
v___x_3649_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3648_);
lean_dec_ref(v_traces_3648_);
v_sz_3650_ = lean_array_size(v___x_3649_);
v___x_3651_ = ((size_t)0ULL);
v___x_3652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__3(v_sz_3650_, v___x_3651_, v___x_3649_);
v_msg_3653_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3653_, 0, v_data_3630_);
lean_ctor_set(v_msg_3653_, 1, v_msg_3632_);
lean_ctor_set(v_msg_3653_, 2, v___x_3652_);
v___x_3654_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_spec__4(v_msg_3653_, v___y_3633_, v___y_3634_, v___x_3645_, v___y_3636_);
lean_dec_ref_known(v___x_3645_, 3);
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3693_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3693_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v_traceState_3660_; lean_object* v_env_3661_; lean_object* v_nextMacroScope_3662_; lean_object* v_ngen_3663_; lean_object* v_auxDeclNGen_3664_; lean_object* v_cache_3665_; lean_object* v_recordedDeps_3666_; lean_object* v_messages_3667_; lean_object* v_infoState_3668_; lean_object* v_snapshotTasks_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3692_; 
v___x_3659_ = lean_st_ref_take(v___y_3636_);
v_traceState_3660_ = lean_ctor_get(v___x_3659_, 4);
v_env_3661_ = lean_ctor_get(v___x_3659_, 0);
v_nextMacroScope_3662_ = lean_ctor_get(v___x_3659_, 1);
v_ngen_3663_ = lean_ctor_get(v___x_3659_, 2);
v_auxDeclNGen_3664_ = lean_ctor_get(v___x_3659_, 3);
v_cache_3665_ = lean_ctor_get(v___x_3659_, 5);
v_recordedDeps_3666_ = lean_ctor_get(v___x_3659_, 6);
v_messages_3667_ = lean_ctor_get(v___x_3659_, 7);
v_infoState_3668_ = lean_ctor_get(v___x_3659_, 8);
v_snapshotTasks_3669_ = lean_ctor_get(v___x_3659_, 9);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3671_ = v___x_3659_;
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_snapshotTasks_3669_);
lean_inc(v_infoState_3668_);
lean_inc(v_messages_3667_);
lean_inc(v_recordedDeps_3666_);
lean_inc(v_cache_3665_);
lean_inc(v_traceState_3660_);
lean_inc(v_auxDeclNGen_3664_);
lean_inc(v_ngen_3663_);
lean_inc(v_nextMacroScope_3662_);
lean_inc(v_env_3661_);
lean_dec(v___x_3659_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
uint64_t v_tid_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3690_; 
v_tid_3673_ = lean_ctor_get_uint64(v_traceState_3660_, sizeof(void*)*1);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_traceState_3660_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; 
v_unused_3691_ = lean_ctor_get(v_traceState_3660_, 0);
lean_dec(v_unused_3691_);
v___x_3675_ = v_traceState_3660_;
v_isShared_3676_ = v_isSharedCheck_3690_;
goto v_resetjp_3674_;
}
else
{
lean_dec(v_traceState_3660_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3690_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3677_ = lean_box(0);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v_ref_3631_);
lean_ctor_set(v___x_3678_, 1, v_a_3655_);
v___x_3679_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3629_, v___x_3678_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3679_);
v___x_3681_ = v___x_3675_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3679_);
lean_ctor_set_uint64(v_reuseFailAlloc_3689_, sizeof(void*)*1, v_tid_3673_);
v___x_3681_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3683_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 4, v___x_3681_);
v___x_3683_ = v___x_3671_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_env_3661_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_nextMacroScope_3662_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_ngen_3663_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_auxDeclNGen_3664_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3688_, 5, v_cache_3665_);
lean_ctor_set(v_reuseFailAlloc_3688_, 6, v_recordedDeps_3666_);
lean_ctor_set(v_reuseFailAlloc_3688_, 7, v_messages_3667_);
lean_ctor_set(v_reuseFailAlloc_3688_, 8, v_infoState_3668_);
lean_ctor_set(v_reuseFailAlloc_3688_, 9, v_snapshotTasks_3669_);
v___x_3683_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3684_ = lean_st_ref_put(v___y_3636_, v___x_3683_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3677_);
v___x_3686_ = v___x_3657_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3677_);
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
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_3629_ = stack[0].m_obj;
lean_object* v_data_3630_ = stack[1].m_obj;
lean_object* v_ref_3631_ = stack[2].m_obj;
lean_object* v_msg_3632_ = stack[3].m_obj;
lean_object* v___y_3633_ = stack[4].m_obj;
lean_object* v___y_3634_ = stack[5].m_obj;
lean_object* v___y_3635_ = stack[6].m_obj;
lean_object* v___y_3636_ = stack[7].m_obj;
lean_object* v_res_3694_;
v_res_3694_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3629_, v_data_3630_, v_ref_3631_, v_msg_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
stack->m_obj
 = v_res_3694_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg___boxed(lean_object* v_oldTraces_3695_, lean_object* v_data_3696_, lean_object* v_ref_3697_, lean_object* v_msg_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3695_, v_data_3696_, v_ref_3697_, v_msg_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(lean_object* v_opts_3705_, lean_object* v_opt_3706_){
_start:
{
lean_object* v_name_3707_; lean_object* v_defValue_3708_; lean_object* v_map_3709_; lean_object* v___x_3710_; 
v_name_3707_ = lean_ctor_get(v_opt_3706_, 0);
v_defValue_3708_ = lean_ctor_get(v_opt_3706_, 1);
v_map_3709_ = lean_ctor_get(v_opts_3705_, 0);
v___x_3710_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3709_, v_name_3707_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_inc(v_defValue_3708_);
return v_defValue_3708_;
}
else
{
lean_object* v_val_3711_; 
v_val_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_val_3711_);
lean_dec_ref_known(v___x_3710_, 1);
if (lean_obj_tag(v_val_3711_) == 3)
{
lean_object* v_v_3712_; 
v_v_3712_ = lean_ctor_get(v_val_3711_, 0);
lean_inc(v_v_3712_);
lean_dec_ref_known(v_val_3711_, 1);
return v_v_3712_;
}
else
{
lean_dec(v_val_3711_);
lean_inc(v_defValue_3708_);
return v_defValue_3708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(lean_object* v_opts_3713_, lean_object* v_opt_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3713_, v_opt_3714_);
lean_dec_ref(v_opt_3714_);
lean_dec_ref(v_opts_3713_);
return v_res_3715_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(lean_object* v_e_3716_){
_start:
{
if (lean_obj_tag(v_e_3716_) == 0)
{
uint8_t v___x_3717_; 
v___x_3717_ = 2;
return v___x_3717_;
}
else
{
uint8_t v___x_3718_; 
v___x_3718_ = 0;
return v___x_3718_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3716_ = stack[0].m_obj;
uint8_t v_res_3719_;
v_res_3719_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_e_3716_);
stack->m_num = v_res_3719_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(lean_object* v_e_3720_){
_start:
{
uint8_t v_res_3721_; lean_object* v_r_3722_; 
v_res_3721_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_e_3720_);
lean_dec_ref(v_e_3720_);
v_r_3722_ = lean_box(v_res_3721_);
return v_r_3722_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3723_; double v___x_3724_; 
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = lean_float_of_nat(v___x_3723_);
return v___x_3724_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1));
v___x_3727_ = l_Lean_stringToMessageData(v___x_3726_);
return v___x_3727_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3728_; double v___x_3729_; 
v___x_3728_ = lean_unsigned_to_nat(1000u);
v___x_3729_ = lean_float_of_nat(v___x_3728_);
return v___x_3729_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object* v_cls_3730_, uint8_t v_collapsed_3731_, lean_object* v_tag_3732_, lean_object* v_opts_3733_, uint8_t v_clsEnabled_3734_, lean_object* v_oldTraces_3735_, lean_object* v_msg_3736_, lean_object* v_resStartStop_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_fst_3748_; lean_object* v_snd_3749_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v_data_3753_; lean_object* v_fst_3764_; lean_object* v_snd_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; lean_object* v___y_3769_; lean_object* v_a_3770_; uint8_t v___y_3785_; double v___y_3817_; 
v_fst_3748_ = lean_ctor_get(v_resStartStop_3737_, 0);
lean_inc(v_fst_3748_);
v_snd_3749_ = lean_ctor_get(v_resStartStop_3737_, 1);
lean_inc(v_snd_3749_);
lean_dec_ref(v_resStartStop_3737_);
v_fst_3764_ = lean_ctor_get(v_snd_3749_, 0);
lean_inc(v_fst_3764_);
v_snd_3765_ = lean_ctor_get(v_snd_3749_, 1);
lean_inc(v_snd_3765_);
lean_dec(v_snd_3749_);
v___x_3766_ = l_Lean_trace_profiler;
v___x_3767_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3733_, v___x_3766_);
if (v___x_3767_ == 0)
{
v___y_3785_ = v___x_3767_;
goto v___jp_3784_;
}
else
{
lean_object* v___x_3822_; uint8_t v___x_3823_; 
v___x_3822_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3823_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_opts_3733_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; double v___x_3826_; double v___x_3827_; double v___x_3828_; 
v___x_3824_ = l_Lean_trace_profiler_threshold;
v___x_3825_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3733_, v___x_3824_);
v___x_3826_ = lean_float_of_nat(v___x_3825_);
v___x_3827_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3);
v___x_3828_ = lean_float_div(v___x_3826_, v___x_3827_);
v___y_3817_ = v___x_3828_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; double v___x_3831_; 
v___x_3829_ = l_Lean_trace_profiler_threshold;
v___x_3830_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_3733_, v___x_3829_);
v___x_3831_ = lean_float_of_nat(v___x_3830_);
v___y_3817_ = v___x_3831_;
goto v___jp_3816_;
}
}
v___jp_3750_:
{
lean_object* v___x_3754_; 
lean_inc(v___y_3752_);
v___x_3754_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_3735_, v_data_3753_, v___y_3752_, v___y_3751_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v___x_3755_; 
lean_dec_ref_known(v___x_3754_, 1);
v___x_3755_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3748_);
return v___x_3755_;
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec(v_fst_3748_);
v_a_3756_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3754_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3754_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
v___jp_3768_:
{
uint8_t v_result_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; double v___x_3774_; lean_object* v_data_3775_; 
v_result_3771_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_fst_3748_);
v___x_3772_ = lean_box(v_result_3771_);
v___x_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
v___x_3774_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0);
lean_inc_ref(v_tag_3732_);
lean_inc_ref(v___x_3773_);
lean_inc(v_cls_3730_);
v_data_3775_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3775_, 0, v_cls_3730_);
lean_ctor_set(v_data_3775_, 1, v___x_3773_);
lean_ctor_set(v_data_3775_, 2, v_tag_3732_);
lean_ctor_set_float(v_data_3775_, sizeof(void*)*3, v___x_3774_);
lean_ctor_set_float(v_data_3775_, sizeof(void*)*3 + 8, v___x_3774_);
lean_ctor_set_uint8(v_data_3775_, sizeof(void*)*3 + 16, v_collapsed_3731_);
if (v___x_3767_ == 0)
{
lean_dec_ref_known(v___x_3773_, 1);
lean_dec(v_snd_3765_);
lean_dec(v_fst_3764_);
lean_dec_ref(v_tag_3732_);
lean_dec(v_cls_3730_);
v___y_3751_ = v_a_3770_;
v___y_3752_ = v___y_3769_;
v_data_3753_ = v_data_3775_;
goto v___jp_3750_;
}
else
{
lean_object* v_data_3776_; double v___x_3777_; double v___x_3778_; 
lean_dec_ref_known(v_data_3775_, 3);
v_data_3776_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3776_, 0, v_cls_3730_);
lean_ctor_set(v_data_3776_, 1, v___x_3773_);
lean_ctor_set(v_data_3776_, 2, v_tag_3732_);
v___x_3777_ = lean_unbox_float(v_fst_3764_);
lean_dec(v_fst_3764_);
lean_ctor_set_float(v_data_3776_, sizeof(void*)*3, v___x_3777_);
v___x_3778_ = lean_unbox_float(v_snd_3765_);
lean_dec(v_snd_3765_);
lean_ctor_set_float(v_data_3776_, sizeof(void*)*3 + 8, v___x_3778_);
lean_ctor_set_uint8(v_data_3776_, sizeof(void*)*3 + 16, v_collapsed_3731_);
v___y_3751_ = v_a_3770_;
v___y_3752_ = v___y_3769_;
v_data_3753_ = v_data_3776_;
goto v___jp_3750_;
}
}
v___jp_3779_:
{
lean_object* v_ref_3780_; lean_object* v___x_3781_; 
v_ref_3780_ = lean_ctor_get(v___y_3745_, 2);
lean_inc(v___y_3746_);
lean_inc_ref(v___y_3745_);
lean_inc(v___y_3744_);
lean_inc_ref(v___y_3743_);
lean_inc(v___y_3742_);
lean_inc_ref(v___y_3741_);
lean_inc(v___y_3740_);
lean_inc_ref(v___y_3739_);
lean_inc(v___y_3738_);
lean_inc(v_fst_3748_);
v___x_3781_ = lean_apply_11(v_msg_3736_, v_fst_3748_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, lean_box(0));
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
v___y_3769_ = v_ref_3780_;
v_a_3770_ = v_a_3782_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3783_; 
lean_dec_ref_known(v___x_3781_, 1);
v___x_3783_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2);
v___y_3769_ = v_ref_3780_;
v_a_3770_ = v___x_3783_;
goto v___jp_3768_;
}
}
v___jp_3784_:
{
if (v_clsEnabled_3734_ == 0)
{
if (v___y_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v_traceState_3787_; lean_object* v_env_3788_; lean_object* v_nextMacroScope_3789_; lean_object* v_ngen_3790_; lean_object* v_auxDeclNGen_3791_; lean_object* v_cache_3792_; lean_object* v_recordedDeps_3793_; lean_object* v_messages_3794_; lean_object* v_infoState_3795_; lean_object* v_snapshotTasks_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_snd_3765_);
lean_dec(v_fst_3764_);
lean_dec_ref(v_msg_3736_);
lean_dec_ref(v_tag_3732_);
lean_dec(v_cls_3730_);
v___x_3786_ = lean_st_ref_take(v___y_3746_);
v_traceState_3787_ = lean_ctor_get(v___x_3786_, 4);
v_env_3788_ = lean_ctor_get(v___x_3786_, 0);
v_nextMacroScope_3789_ = lean_ctor_get(v___x_3786_, 1);
v_ngen_3790_ = lean_ctor_get(v___x_3786_, 2);
v_auxDeclNGen_3791_ = lean_ctor_get(v___x_3786_, 3);
v_cache_3792_ = lean_ctor_get(v___x_3786_, 5);
v_recordedDeps_3793_ = lean_ctor_get(v___x_3786_, 6);
v_messages_3794_ = lean_ctor_get(v___x_3786_, 7);
v_infoState_3795_ = lean_ctor_get(v___x_3786_, 8);
v_snapshotTasks_3796_ = lean_ctor_get(v___x_3786_, 9);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3798_ = v___x_3786_;
v_isShared_3799_ = v_isSharedCheck_3815_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_snapshotTasks_3796_);
lean_inc(v_infoState_3795_);
lean_inc(v_messages_3794_);
lean_inc(v_recordedDeps_3793_);
lean_inc(v_cache_3792_);
lean_inc(v_traceState_3787_);
lean_inc(v_auxDeclNGen_3791_);
lean_inc(v_ngen_3790_);
lean_inc(v_nextMacroScope_3789_);
lean_inc(v_env_3788_);
lean_dec(v___x_3786_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3815_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
uint64_t v_tid_3800_; lean_object* v_traces_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3814_; 
v_tid_3800_ = lean_ctor_get_uint64(v_traceState_3787_, sizeof(void*)*1);
v_traces_3801_ = lean_ctor_get(v_traceState_3787_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_traceState_3787_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3803_ = v_traceState_3787_;
v_isShared_3804_ = v_isSharedCheck_3814_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_traces_3801_);
lean_dec(v_traceState_3787_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3814_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3735_, v_traces_3801_);
lean_dec_ref(v_traces_3801_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v___x_3805_);
v___x_3807_ = v___x_3803_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3805_);
lean_ctor_set_uint64(v_reuseFailAlloc_3813_, sizeof(void*)*1, v_tid_3800_);
v___x_3807_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3809_; 
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 4, v___x_3807_);
v___x_3809_ = v___x_3798_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_env_3788_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_nextMacroScope_3789_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_ngen_3790_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v_auxDeclNGen_3791_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3812_, 5, v_cache_3792_);
lean_ctor_set(v_reuseFailAlloc_3812_, 6, v_recordedDeps_3793_);
lean_ctor_set(v_reuseFailAlloc_3812_, 7, v_messages_3794_);
lean_ctor_set(v_reuseFailAlloc_3812_, 8, v_infoState_3795_);
lean_ctor_set(v_reuseFailAlloc_3812_, 9, v_snapshotTasks_3796_);
v___x_3809_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = lean_st_ref_put(v___y_3746_, v___x_3809_);
v___x_3811_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_fst_3748_);
return v___x_3811_;
}
}
}
}
}
else
{
goto v___jp_3779_;
}
}
else
{
goto v___jp_3779_;
}
}
v___jp_3816_:
{
double v___x_3818_; double v___x_3819_; double v___x_3820_; uint8_t v___x_3821_; 
v___x_3818_ = lean_unbox_float(v_snd_3765_);
v___x_3819_ = lean_unbox_float(v_fst_3764_);
v___x_3820_ = lean_float_sub(v___x_3818_, v___x_3819_);
v___x_3821_ = lean_float_decLt(v___y_3817_, v___x_3820_);
v___y_3785_ = v___x_3821_;
goto v___jp_3784_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3730_ = stack[0].m_obj;
uint8_t v_collapsed_3731_ = stack[1].m_num;
lean_object* v_tag_3732_ = stack[2].m_obj;
lean_object* v_opts_3733_ = stack[3].m_obj;
uint8_t v_clsEnabled_3734_ = stack[4].m_num;
lean_object* v_oldTraces_3735_ = stack[5].m_obj;
lean_object* v_msg_3736_ = stack[6].m_obj;
lean_object* v_resStartStop_3737_ = stack[7].m_obj;
lean_object* v___y_3738_ = stack[8].m_obj;
lean_object* v___y_3739_ = stack[9].m_obj;
lean_object* v___y_3740_ = stack[10].m_obj;
lean_object* v___y_3741_ = stack[11].m_obj;
lean_object* v___y_3742_ = stack[12].m_obj;
lean_object* v___y_3743_ = stack[13].m_obj;
lean_object* v___y_3744_ = stack[14].m_obj;
lean_object* v___y_3745_ = stack[15].m_obj;
lean_object* v___y_3746_ = stack[16].m_obj;
lean_object* v_res_3832_;
v_res_3832_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_cls_3730_, v_collapsed_3731_, v_tag_3732_, v_opts_3733_, v_clsEnabled_3734_, v_oldTraces_3735_, v_msg_3736_, v_resStartStop_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
stack->m_obj
 = v_res_3832_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object** _args){
lean_object* v_cls_3833_ = _args[0];
lean_object* v_collapsed_3834_ = _args[1];
lean_object* v_tag_3835_ = _args[2];
lean_object* v_opts_3836_ = _args[3];
lean_object* v_clsEnabled_3837_ = _args[4];
lean_object* v_oldTraces_3838_ = _args[5];
lean_object* v_msg_3839_ = _args[6];
lean_object* v_resStartStop_3840_ = _args[7];
lean_object* v___y_3841_ = _args[8];
lean_object* v___y_3842_ = _args[9];
lean_object* v___y_3843_ = _args[10];
lean_object* v___y_3844_ = _args[11];
lean_object* v___y_3845_ = _args[12];
lean_object* v___y_3846_ = _args[13];
lean_object* v___y_3847_ = _args[14];
lean_object* v___y_3848_ = _args[15];
lean_object* v___y_3849_ = _args[16];
lean_object* v___y_3850_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3851_; uint8_t v_clsEnabled_boxed_3852_; lean_object* v_res_3853_; 
v_collapsed_boxed_3851_ = lean_unbox(v_collapsed_3834_);
v_clsEnabled_boxed_3852_ = lean_unbox(v_clsEnabled_3837_);
v_res_3853_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_cls_3833_, v_collapsed_boxed_3851_, v_tag_3835_, v_opts_3836_, v_clsEnabled_boxed_3852_, v_oldTraces_3838_, v_msg_3839_, v_resStartStop_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v_opts_3836_);
return v_res_3853_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0));
v___x_3856_ = l_Lean_stringToMessageData(v___x_3855_);
return v___x_3856_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2));
v___x_3859_ = l_Lean_stringToMessageData(v___x_3858_);
return v___x_3859_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4));
v___x_3862_ = l_Lean_stringToMessageData(v___x_3861_);
return v___x_3862_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6));
v___x_3865_ = l_Lean_stringToMessageData(v___x_3864_);
return v___x_3865_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8));
v___x_3868_ = l_Lean_stringToMessageData(v___x_3867_);
return v___x_3868_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11(void){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10));
v___x_3871_ = l_Lean_stringToMessageData(v___x_3870_);
return v___x_3871_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(lean_object* v___x_3872_, lean_object* v_e_3873_, lean_object* v_x_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
if (lean_obj_tag(v_x_3874_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v_e_3873_);
v_a_3885_ = lean_ctor_get(v_x_3874_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_x_3874_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3887_ = v_x_3874_;
v_isShared_3888_ = v_isSharedCheck_3899_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v_x_3874_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3899_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3890_ = l_Lean_MessageData_ofName(v___x_3872_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = l_Lean_Exception_toMessageData(v_a_3885_);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3895_);
v___x_3897_ = v___x_3887_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3938_; 
v_a_3900_ = lean_ctor_get(v_x_3874_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_x_3874_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3902_ = v_x_3874_;
v_isShared_3903_ = v_isSharedCheck_3938_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v_x_3874_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3938_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
if (lean_obj_tag(v_a_3900_) == 0)
{
uint8_t v_done_3904_; 
v_done_3904_ = lean_ctor_get_uint8(v_a_3900_, 0);
lean_dec_ref_known(v_a_3900_, 0);
if (v_done_3904_ == 1)
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3905_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3906_ = l_Lean_MessageData_ofName(v___x_3872_);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = l_Lean_indentExpr(v_e_3873_);
v___x_3911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3911_);
v___x_3913_ = v___x_3902_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_dec_ref(v_e_3873_);
v___x_3915_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3916_ = l_Lean_MessageData_ofName(v___x_3872_);
v___x_3917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7);
v___x_3919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3919_);
v___x_3921_ = v___x_3902_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
else
{
lean_object* v_e_x27_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3936_; 
v_e_x27_3923_ = lean_ctor_get(v_a_3900_, 0);
lean_inc_ref(v_e_x27_3923_);
lean_dec_ref_known(v_a_3900_, 2);
v___x_3924_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
v___x_3925_ = l_Lean_MessageData_ofName(v___x_3872_);
v___x_3926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9);
v___x_3928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3926_);
lean_ctor_set(v___x_3928_, 1, v___x_3927_);
v___x_3929_ = l_Lean_indentExpr(v_e_3873_);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = l_Lean_indentExpr(v_e_x27_3923_);
v___x_3934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3934_);
v___x_3936_ = v___x_3902_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3872_ = stack[0].m_obj;
lean_object* v_e_3873_ = stack[1].m_obj;
lean_object* v_x_3874_ = stack[2].m_obj;
lean_object* v___y_3875_ = stack[3].m_obj;
lean_object* v___y_3876_ = stack[4].m_obj;
lean_object* v___y_3877_ = stack[5].m_obj;
lean_object* v___y_3878_ = stack[6].m_obj;
lean_object* v___y_3879_ = stack[7].m_obj;
lean_object* v___y_3880_ = stack[8].m_obj;
lean_object* v___y_3881_ = stack[9].m_obj;
lean_object* v___y_3882_ = stack[10].m_obj;
lean_object* v___y_3883_ = stack[11].m_obj;
lean_object* v_res_3939_;
v_res_3939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(v___x_3872_, v_e_3873_, v_x_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
stack->m_obj
 = v_res_3939_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(lean_object* v___x_3940_, lean_object* v_e_3941_, lean_object* v_x_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(v___x_3940_, v_e_3941_, v_x_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
return v_res_3953_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_3979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8));
v___x_3980_ = l_Lean_Name_append(v___x_3979_, v___x_3978_);
return v___x_3980_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10(void){
_start:
{
lean_object* v___x_3981_; double v___x_3982_; 
v___x_3981_ = lean_unsigned_to_nat(1000000000u);
v___x_3982_ = lean_float_of_nat(v___x_3981_);
return v___x_3982_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object* v_erased_3983_, lean_object* v_e_3984_, lean_object* v_as_3985_, size_t v_sz_3986_, size_t v_i_3987_, lean_object* v_b_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_a_4000_; uint8_t v___x_4004_; 
v___x_4004_ = lean_usize_dec_lt(v_i_3987_, v_sz_3986_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; 
lean_dec_ref(v_e_3984_);
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v_b_3988_);
return v___x_4005_;
}
else
{
lean_object* v_a_4006_; lean_object* v_fst_4007_; lean_object* v_toCbvSimprocOLeanEntry_4008_; lean_object* v_snd_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_b_3988_);
v_a_4006_ = lean_array_uget(v_as_3985_, v_i_3987_);
v_fst_4007_ = lean_ctor_get(v_a_4006_, 0);
lean_inc(v_fst_4007_);
v_toCbvSimprocOLeanEntry_4008_ = lean_ctor_get(v_fst_4007_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_4008_);
v_snd_4009_ = lean_ctor_get(v_a_4006_, 1);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_a_4006_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; 
v_unused_4151_ = lean_ctor_get(v_a_4006_, 0);
lean_dec(v_unused_4151_);
v___x_4011_ = v_a_4006_;
v_isShared_4012_ = v_isSharedCheck_4150_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_snd_4009_);
lean_dec(v_a_4006_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4150_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v_proc_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4148_; 
v_proc_4013_ = lean_ctor_get(v_fst_4007_, 1);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_fst_4007_);
if (v_isSharedCheck_4148_ == 0)
{
lean_object* v_unused_4149_; 
v_unused_4149_ = lean_ctor_get(v_fst_4007_, 0);
lean_dec(v_unused_4149_);
v___x_4015_ = v_fst_4007_;
v_isShared_4016_ = v_isSharedCheck_4148_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_proc_4013_);
lean_dec(v_fst_4007_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4148_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v_declName_4017_; lean_object* v___x_4018_; lean_object* v___y_4020_; lean_object* v___y_4027_; lean_object* v___x_4033_; lean_object* v___y_4035_; uint8_t v___y_4036_; uint8_t v___x_4037_; lean_object* v___y_4039_; 
v_declName_4017_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_4008_, 0);
lean_inc(v_declName_4017_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_4008_);
v___x_4018_ = lean_box(0);
v___x_4033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v___x_4037_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_erased_3983_, v_declName_4017_);
if (v___x_4037_ == 0)
{
lean_object* v_toCold_4051_; lean_object* v_options_4052_; lean_object* v_inheritedTraceOptions_4053_; uint8_t v_hasTrace_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; 
v_toCold_4051_ = lean_ctor_get(v___y_3996_, 0);
v_options_4052_ = lean_ctor_get(v_toCold_4051_, 2);
v_inheritedTraceOptions_4053_ = lean_ctor_get(v_toCold_4051_, 11);
v_hasTrace_4054_ = lean_ctor_get_uint8(v_options_4052_, sizeof(void*)*1);
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = lean_nat_dec_eq(v_snd_4009_, v___x_4055_);
if (v_hasTrace_4054_ == 0)
{
lean_object* v___x_4057_; 
lean_dec(v_declName_4017_);
lean_inc_ref(v_e_3984_);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_4056_, v_e_3984_, v_snd_4009_, v_proc_4013_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v_snd_4009_);
v___y_4039_ = v___x_4057_;
goto v___jp_4038_;
}
else
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___f_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v_a_4072_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v_a_4087_; 
v___x_4058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1));
v___x_4059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2));
v___x_4060_ = l_Lean_privateToUserName(v_declName_4017_);
v___x_4061_ = lean_box(0);
v___x_4062_ = l_Lean_Name_replacePrefix(v___x_4060_, v___x_4058_, v___x_4061_);
v___x_4063_ = l_Lean_Name_replacePrefix(v___x_4062_, v___x_4059_, v___x_4061_);
lean_inc_ref(v_e_3984_);
v___f_4064_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed), 13, 2);
lean_closure_set(v___f_4064_, 0, v___x_4063_);
lean_closure_set(v___f_4064_, 1, v_e_3984_);
v___x_4065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5));
v___x_4066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6));
v___x_4067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9);
v___x_4068_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4053_, v_options_4052_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4145_; uint8_t v___x_4146_; 
v___x_4145_ = l_Lean_trace_profiler;
v___x_4146_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_4052_, v___x_4145_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; 
lean_dec_ref(v___f_4064_);
lean_inc_ref(v_e_3984_);
v___x_4147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_4056_, v_e_3984_, v_snd_4009_, v_proc_4013_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v_snd_4009_);
v___y_4039_ = v___x_4147_;
goto v___jp_4038_;
}
else
{
goto v___jp_4096_;
}
}
else
{
goto v___jp_4096_;
}
v___jp_4069_:
{
lean_object* v___x_4073_; double v___x_4074_; double v___x_4075_; double v___x_4076_; double v___x_4077_; double v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4073_ = lean_io_mono_nanos_now();
v___x_4074_ = lean_float_of_nat(v___y_4070_);
v___x_4075_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10);
v___x_4076_ = lean_float_div(v___x_4074_, v___x_4075_);
v___x_4077_ = lean_float_of_nat(v___x_4073_);
v___x_4078_ = lean_float_div(v___x_4077_, v___x_4075_);
v___x_4079_ = lean_box_float(v___x_4076_);
v___x_4080_ = lean_box_float(v___x_4078_);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v_a_4072_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_4065_, v_hasTrace_4054_, v___x_4066_, v_options_4052_, v___x_4068_, v___y_4071_, v___f_4064_, v___x_4082_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
v___y_4039_ = v___x_4083_;
goto v___jp_4038_;
}
v___jp_4084_:
{
lean_object* v___x_4088_; double v___x_4089_; double v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4088_ = lean_io_get_num_heartbeats();
v___x_4089_ = lean_float_of_nat(v___y_4085_);
v___x_4090_ = lean_float_of_nat(v___x_4088_);
v___x_4091_ = lean_box_float(v___x_4089_);
v___x_4092_ = lean_box_float(v___x_4090_);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4094_, 0, v_a_4087_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_4065_, v_hasTrace_4054_, v___x_4066_, v_options_4052_, v___x_4068_, v___y_4086_, v___f_4064_, v___x_4094_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
v___y_4039_ = v___x_4095_;
goto v___jp_4038_;
}
v___jp_4096_:
{
lean_object* v___x_4097_; 
v___x_4097_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_3997_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4097_, 1);
v___x_4099_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4100_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_4052_, v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = lean_io_mono_nanos_now();
lean_inc_ref(v_e_3984_);
v___x_4102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_4056_, v_e_3984_, v_snd_4009_, v_proc_4013_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v_snd_4009_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set_tag(v___x_4105_, 1);
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
v___y_4070_ = v___x_4101_;
v___y_4071_ = v_a_4098_;
v_a_4072_ = v___x_4108_;
goto v___jp_4069_;
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_a_4111_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4102_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4102_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
lean_ctor_set_tag(v___x_4113_, 0);
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
v___y_4070_ = v___x_4101_;
v___y_4071_ = v_a_4098_;
v_a_4072_ = v___x_4116_;
goto v___jp_4069_;
}
}
}
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_e_3984_);
v___x_4120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_4056_, v_e_3984_, v_snd_4009_, v_proc_4013_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v_snd_4009_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4123_ = v___x_4120_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4120_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
lean_ctor_set_tag(v___x_4123_, 1);
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
v___y_4085_ = v___x_4119_;
v___y_4086_ = v_a_4098_;
v_a_4087_ = v___x_4126_;
goto v___jp_4084_;
}
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
v_a_4129_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4120_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4120_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
lean_ctor_set_tag(v___x_4131_, 0);
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
v___y_4085_ = v___x_4119_;
v___y_4086_ = v_a_4098_;
v_a_4087_ = v___x_4134_;
goto v___jp_4084_;
}
}
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v___f_4064_);
lean_del_object(v___x_4015_);
lean_dec_ref(v_proc_4013_);
lean_del_object(v___x_4011_);
lean_dec(v_snd_4009_);
lean_dec_ref(v_e_3984_);
v_a_4137_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4097_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4097_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_4017_);
lean_del_object(v___x_4015_);
lean_dec_ref(v_proc_4013_);
lean_del_object(v___x_4011_);
lean_dec(v_snd_4009_);
v_a_4000_ = v___x_4033_;
goto v___jp_3999_;
}
v___jp_4019_:
{
lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___y_4020_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 1, v___x_4018_);
lean_ctor_set(v___x_4011_, 0, v___x_4021_);
v___x_4023_ = v___x_4011_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4025_, 1, v___x_4018_);
v___x_4023_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
}
v___jp_4026_:
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___y_4027_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 1, v___x_4018_);
lean_ctor_set(v___x_4015_, 0, v___x_4028_);
v___x_4030_ = v___x_4015_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4032_, 1, v___x_4018_);
v___x_4030_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
}
v___jp_4034_:
{
if (v___y_4036_ == 0)
{
lean_dec_ref(v___y_4035_);
lean_del_object(v___x_4011_);
v_a_4000_ = v___x_4033_;
goto v___jp_3999_;
}
else
{
lean_dec_ref(v_e_3984_);
v___y_4020_ = v___y_4035_;
goto v___jp_4019_;
}
}
v___jp_4038_:
{
if (lean_obj_tag(v___y_4039_) == 0)
{
lean_object* v_a_4040_; 
v_a_4040_ = lean_ctor_get(v___y_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___y_4039_, 1);
if (lean_obj_tag(v_a_4040_) == 1)
{
lean_del_object(v___x_4011_);
lean_dec_ref(v_e_3984_);
v___y_4027_ = v_a_4040_;
goto v___jp_4026_;
}
else
{
if (v___x_4037_ == 0)
{
lean_del_object(v___x_4015_);
if (lean_obj_tag(v_a_4040_) == 0)
{
uint8_t v_done_4041_; 
v_done_4041_ = lean_ctor_get_uint8(v_a_4040_, 0);
if (v_done_4041_ == 1)
{
uint8_t v_contextDependent_4042_; 
v_contextDependent_4042_ = lean_ctor_get_uint8(v_a_4040_, 1);
if (v_contextDependent_4042_ == 0)
{
lean_dec_ref(v_e_3984_);
v___y_4020_ = v_a_4040_;
goto v___jp_4019_;
}
else
{
v___y_4035_ = v_a_4040_;
v___y_4036_ = v___x_4037_;
goto v___jp_4034_;
}
}
else
{
v___y_4035_ = v_a_4040_;
v___y_4036_ = v___x_4037_;
goto v___jp_4034_;
}
}
else
{
v___y_4035_ = v_a_4040_;
v___y_4036_ = v___x_4037_;
goto v___jp_4034_;
}
}
else
{
lean_del_object(v___x_4011_);
lean_dec_ref(v_e_3984_);
v___y_4027_ = v_a_4040_;
goto v___jp_4026_;
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_del_object(v___x_4015_);
lean_del_object(v___x_4011_);
lean_dec_ref(v_e_3984_);
v_a_4043_ = lean_ctor_get(v___y_4039_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___y_4039_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___y_4039_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___y_4039_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
}
}
v___jp_3999_:
{
size_t v___x_4001_; size_t v___x_4002_; 
v___x_4001_ = ((size_t)1ULL);
v___x_4002_ = lean_usize_add(v_i_3987_, v___x_4001_);
lean_inc_ref(v_a_4000_);
v_i_3987_ = v___x_4002_;
v_b_3988_ = v_a_4000_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_erased_3983_ = stack[0].m_obj;
lean_object* v_e_3984_ = stack[1].m_obj;
lean_object* v_as_3985_ = stack[2].m_obj;
size_t v_sz_3986_ = stack[3].m_num;
size_t v_i_3987_ = stack[4].m_num;
lean_object* v_b_3988_ = stack[5].m_obj;
lean_object* v___y_3989_ = stack[6].m_obj;
lean_object* v___y_3990_ = stack[7].m_obj;
lean_object* v___y_3991_ = stack[8].m_obj;
lean_object* v___y_3992_ = stack[9].m_obj;
lean_object* v___y_3993_ = stack[10].m_obj;
lean_object* v___y_3994_ = stack[11].m_obj;
lean_object* v___y_3995_ = stack[12].m_obj;
lean_object* v___y_3996_ = stack[13].m_obj;
lean_object* v___y_3997_ = stack[14].m_obj;
lean_object* v_res_4152_;
v_res_4152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_3983_, v_e_3984_, v_as_3985_, v_sz_3986_, v_i_3987_, v_b_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
stack->m_obj
 = v_res_4152_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object* v_erased_4153_, lean_object* v_e_4154_, lean_object* v_as_4155_, lean_object* v_sz_4156_, lean_object* v_i_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
size_t v_sz_boxed_4169_; size_t v_i_boxed_4170_; lean_object* v_res_4171_; 
v_sz_boxed_4169_ = lean_unbox_usize(v_sz_4156_);
lean_dec(v_sz_4156_);
v_i_boxed_4170_ = lean_unbox_usize(v_i_4157_);
lean_dec(v_i_4157_);
v_res_4171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_4153_, v_e_4154_, v_as_4155_, v_sz_boxed_4169_, v_i_boxed_4170_, v_b_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v_as_4155_);
lean_dec_ref(v_erased_4153_);
return v_res_4171_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object* v_tree_4174_, lean_object* v_erased_4175_, lean_object* v_e_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___x_4187_; lean_object* v_mctx_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4187_ = lean_st_ref_get(v_a_4183_);
v_mctx_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc_ref(v_mctx_4188_);
lean_dec(v___x_4187_);
v___x_4189_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_mctx_4188_, v_tree_4174_, v_e_4176_);
lean_dec_ref(v_mctx_4188_);
v___x_4190_ = lean_array_get_size(v___x_4189_);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = lean_nat_dec_eq(v___x_4190_, v___x_4191_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; size_t v_sz_4194_; size_t v___x_4195_; lean_object* v___x_4196_; 
v___x_4193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v_sz_4194_ = lean_array_size(v___x_4189_);
v___x_4195_ = ((size_t)0ULL);
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_4175_, v_e_4176_, v___x_4189_, v_sz_4194_, v___x_4195_, v___x_4193_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec_ref(v___x_4189_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4210_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4199_ = v___x_4196_;
v_isShared_4200_ = v_isSharedCheck_4210_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4196_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4210_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v_fst_4201_; 
v_fst_4201_ = lean_ctor_get(v_a_4197_, 0);
lean_inc(v_fst_4201_);
lean_dec(v_a_4197_);
if (lean_obj_tag(v_fst_4201_) == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4204_; 
v___x_4202_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4202_, 0, v___x_4192_);
lean_ctor_set_uint8(v___x_4202_, 1, v___x_4192_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4202_);
v___x_4204_ = v___x_4199_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4202_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
else
{
lean_object* v_val_4206_; lean_object* v___x_4208_; 
v_val_4206_ = lean_ctor_get(v_fst_4201_, 0);
lean_inc(v_val_4206_);
lean_dec_ref_known(v_fst_4201_, 1);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v_val_4206_);
v___x_4208_ = v___x_4199_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_val_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_a_4211_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4196_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4196_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
lean_dec_ref(v___x_4189_);
lean_dec_ref(v_e_4176_);
v___x_4219_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0));
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
return v___x_4220_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_tree_4174_ = stack[0].m_obj;
lean_object* v_erased_4175_ = stack[1].m_obj;
lean_object* v_e_4176_ = stack[2].m_obj;
lean_object* v_a_4177_ = stack[3].m_obj;
lean_object* v_a_4178_ = stack[4].m_obj;
lean_object* v_a_4179_ = stack[5].m_obj;
lean_object* v_a_4180_ = stack[6].m_obj;
lean_object* v_a_4181_ = stack[7].m_obj;
lean_object* v_a_4182_ = stack[8].m_obj;
lean_object* v_a_4183_ = stack[9].m_obj;
lean_object* v_a_4184_ = stack[10].m_obj;
lean_object* v_a_4185_ = stack[11].m_obj;
lean_object* v_res_4221_;
v_res_4221_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_tree_4174_, v_erased_4175_, v_e_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
stack->m_obj
 = v_res_4221_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object* v_tree_4222_, lean_object* v_erased_4223_, lean_object* v_e_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_tree_4222_, v_erased_4223_, v_e_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
lean_dec(v_a_4227_);
lean_dec_ref(v_a_4226_);
lean_dec(v_a_4225_);
lean_dec_ref(v_erased_4223_);
lean_dec_ref(v_tree_4222_);
return v_res_4235_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_object* v_00_u03b1_4236_, lean_object* v_x_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_x_4237_);
return v___x_4248_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4237_ = stack[1].m_obj;
lean_object* v___y_4238_ = stack[2].m_obj;
lean_object* v___y_4239_ = stack[3].m_obj;
lean_object* v___y_4240_ = stack[4].m_obj;
lean_object* v___y_4241_ = stack[5].m_obj;
lean_object* v___y_4242_ = stack[6].m_obj;
lean_object* v___y_4243_ = stack[7].m_obj;
lean_object* v___y_4244_ = stack[8].m_obj;
lean_object* v___y_4245_ = stack[9].m_obj;
lean_object* v___y_4246_ = stack[10].m_obj;
lean_object* v_res_4249_;
v_res_4249_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(lean_box(0), v_x_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
stack->m_obj
 = v_res_4249_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4250_, lean_object* v_x_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(v_00_u03b1_4250_, v_x_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
return v_res_4262_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(lean_object* v_oldTraces_4263_, lean_object* v_data_4264_, lean_object* v_ref_4265_, lean_object* v_msg_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___redArg(v_oldTraces_4263_, v_data_4264_, v_ref_4265_, v_msg_4266_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_4263_ = stack[0].m_obj;
lean_object* v_data_4264_ = stack[1].m_obj;
lean_object* v_ref_4265_ = stack[2].m_obj;
lean_object* v_msg_4266_ = stack[3].m_obj;
lean_object* v___y_4267_ = stack[4].m_obj;
lean_object* v___y_4268_ = stack[5].m_obj;
lean_object* v___y_4269_ = stack[6].m_obj;
lean_object* v___y_4270_ = stack[7].m_obj;
lean_object* v___y_4271_ = stack[8].m_obj;
lean_object* v___y_4272_ = stack[9].m_obj;
lean_object* v___y_4273_ = stack[10].m_obj;
lean_object* v___y_4274_ = stack[11].m_obj;
lean_object* v___y_4275_ = stack[12].m_obj;
lean_object* v_res_4278_;
v_res_4278_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_oldTraces_4263_, v_data_4264_, v_ref_4265_, v_msg_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
stack->m_obj
 = v_res_4278_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(lean_object* v_oldTraces_4279_, lean_object* v_data_4280_, lean_object* v_ref_4281_, lean_object* v_msg_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_oldTraces_4279_, v_data_4280_, v_ref_4281_, v_msg_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
return v_res_4293_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default();
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase();
l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase = _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs);
l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef);
lean_dec_ref(res);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
}
#ifdef __cplusplus
}
#endif
