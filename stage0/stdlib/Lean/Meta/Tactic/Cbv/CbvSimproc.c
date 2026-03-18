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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprName___private__1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_initializing();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_Sym_getMatchWithExtra___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs;
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cbvSimprocDeclExt"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 182, 205, 129, 188, 54, 74, 13)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___closed__0_value;
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Invalid cbv simproc declaration `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: It is declared in an imported module"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "cbvSimprocExt"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 184, 164, 42, 54, 246, 220, 149)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simproc "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ": done"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": no change"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n==>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 118, 156, 162, 140, 167, 154, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simprocs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 69, 90, 123, 228, 205, 71, 22)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(lean_object* v_pre_28_){
_start:
{
lean_inc(v_pre_28_);
return v_pre_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg___boxed(lean_object* v_pre_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(v_pre_29_);
lean_dec(v_pre_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_pre_34_){
_start:
{
lean_inc(v_pre_34_);
return v_pre_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_pre_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_pre_38_);
lean_dec(v_pre_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(lean_object* v_eval_41_){
_start:
{
lean_inc(v_eval_41_);
return v_eval_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg___boxed(lean_object* v_eval_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(v_eval_42_);
lean_dec(v_eval_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_eval_47_){
_start:
{
lean_inc(v_eval_47_);
return v_eval_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_eval_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_eval_51_);
lean_dec(v_eval_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(lean_object* v_post_54_){
_start:
{
lean_inc(v_post_54_);
return v_post_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg___boxed(lean_object* v_post_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(v_post_55_);
lean_dec(v_post_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_post_60_){
_start:
{
lean_inc(v_post_60_);
return v_post_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_post_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_post_64_);
lean_dec(v_post_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(uint8_t v_x_69_, uint8_t v_y_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_69_);
v___x_72_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_y_70_);
v___x_73_ = lean_nat_dec_eq(v___x_71_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_17__boxed_76_; uint8_t v_y_18__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_17__boxed_76_ = lean_unbox(v_x_74_);
v_y_18__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(v_x_17__boxed_76_, v_y_18__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(uint8_t v_x_82_){
_start:
{
switch(v_x_82_)
{
case 0:
{
uint64_t v___x_83_; 
v___x_83_ = 0ULL;
return v___x_83_;
}
case 1:
{
uint64_t v___x_84_; 
v___x_84_ = 1ULL;
return v___x_84_;
}
default: 
{
uint64_t v___x_85_; 
v___x_85_ = 2ULL;
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed(lean_object* v_x_86_){
_start:
{
uint8_t v_x_40__boxed_87_; uint64_t v_res_88_; lean_object* v_r_89_; 
v_x_40__boxed_87_ = lean_unbox(v_x_86_);
v_res_88_ = l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(v_x_40__boxed_87_);
v_r_89_ = lean_box_uint64(v_res_88_);
return v_r_89_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_nat_to_int(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_to_int(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(uint8_t v_x_105_, lean_object* v_prec_106_){
_start:
{
lean_object* v___y_108_; lean_object* v___y_115_; lean_object* v___y_122_; 
switch(v_x_105_)
{
case 0:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1024u);
v___x_129_ = lean_nat_dec_le(v___x_128_, v_prec_106_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_108_ = v___x_130_;
goto v___jp_107_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_108_ = v___x_131_;
goto v___jp_107_;
}
}
case 1:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1024u);
v___x_133_ = lean_nat_dec_le(v___x_132_, v_prec_106_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_115_ = v___x_134_;
goto v___jp_114_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_115_ = v___x_135_;
goto v___jp_114_;
}
}
default: 
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(1024u);
v___x_137_ = lean_nat_dec_le(v___x_136_, v_prec_106_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
v___y_122_ = v___x_138_;
goto v___jp_121_;
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7, &l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
v___y_122_ = v___x_139_;
goto v___jp_121_;
}
}
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_109_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1));
v___x_110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_110_, 0, v___y_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = 0;
v___x_112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_111_);
v___x_113_ = l_Repr_addAppParen(v___x_112_, v_prec_106_);
return v___x_113_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_116_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3));
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___y_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = l_Repr_addAppParen(v___x_119_, v_prec_106_);
return v___x_120_;
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5));
v___x_124_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_124_, 0, v___y_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = 0;
v___x_126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_125_);
v___x_127_ = l_Repr_addAppParen(v___x_126_, v_prec_106_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed(lean_object* v_x_140_, lean_object* v_prec_141_){
_start:
{
uint8_t v_x_177__boxed_142_; lean_object* v_res_143_; 
v_x_177__boxed_142_ = lean_unbox(v_x_140_);
v_res_143_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(v_x_177__boxed_142_, v_prec_141_);
lean_dec(v_prec_141_);
return v_res_143_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_box(0);
v___x_160_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6));
v___x_161_ = l_Lean_mkConst(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_box(0);
v___x_171_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9));
v___x_172_ = l_Lean_mkConst(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_box(0);
v___x_182_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12));
v___x_183_ = l_Lean_mkConst(v___x_182_, v___x_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(uint8_t v_x_184_){
_start:
{
switch(v_x_184_)
{
case 0:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
return v___x_185_;
}
case 1:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
return v___x_186_;
}
default: 
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed(lean_object* v_x_188_){
_start:
{
uint8_t v_x_196__boxed_189_; lean_object* v_res_190_; 
v_x_196__boxed_189_ = lean_unbox(v_x_188_);
v_res_190_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(v_x_196__boxed_189_);
return v_res_190_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_box(0);
v___x_199_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1));
v___x_200_ = l_Lean_mkConst(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3(void){
_start:
{
lean_object* v___x_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2);
v___f_202_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0));
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___f_202_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3);
return v___x_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(lean_object* v_e_u2081_213_, lean_object* v_e_u2082_214_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_215_; lean_object* v_toCbvSimprocOLeanEntry_216_; lean_object* v_declName_217_; lean_object* v_declName_218_; uint8_t v___x_219_; 
v_toCbvSimprocOLeanEntry_215_ = lean_ctor_get(v_e_u2081_213_, 0);
v_toCbvSimprocOLeanEntry_216_ = lean_ctor_get(v_e_u2082_214_, 0);
v_declName_217_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_215_, 0);
v_declName_218_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_216_, 0);
v___x_219_ = lean_name_eq(v_declName_217_, v_declName_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed(lean_object* v_e_u2081_220_, lean_object* v_e_u2082_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(v_e_u2081_220_, v_e_u2082_221_);
lean_dec_ref(v_e_u2082_221_);
lean_dec_ref(v_e_u2081_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0(lean_object* v_e_226_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_227_; lean_object* v_declName_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_toCbvSimprocOLeanEntry_227_ = lean_ctor_get(v_e_226_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_227_);
lean_dec_ref(v_e_226_);
v_declName_228_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_227_, 0);
lean_inc(v_declName_228_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_227_);
v___x_229_ = 1;
v___x_230_ = l_Lean_Name_toString(v_declName_228_, v___x_229_);
v___x_231_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_234_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_object* v_00_u03b2_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(lean_box(0));
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2);
v___x_244_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1);
v___x_245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
lean_ctor_set(v___x_245_, 3, v___x_243_);
lean_ctor_set(v___x_245_, 4, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
return v___x_247_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(lean_object* v_msg_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0);
v___x_251_ = lean_panic_fn(v___x_250_, v_msg_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_ks_256_; lean_object* v_vs_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_281_; 
v_ks_256_ = lean_ctor_get(v_x_252_, 0);
v_vs_257_ = lean_ctor_get(v_x_252_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_252_);
if (v_isSharedCheck_281_ == 0)
{
v___x_259_ = v_x_252_;
v_isShared_260_ = v_isSharedCheck_281_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_vs_257_);
lean_inc(v_ks_256_);
lean_dec(v_x_252_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_281_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_array_get_size(v_ks_256_);
v___x_262_ = lean_nat_dec_lt(v_x_253_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec(v_x_253_);
v___x_263_ = lean_array_push(v_ks_256_, v_x_254_);
v___x_264_ = lean_array_push(v_vs_257_, v_x_255_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_264_);
lean_ctor_set(v___x_259_, 0, v___x_263_);
v___x_266_ = v___x_259_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
else
{
lean_object* v_k_x27_268_; uint8_t v___x_269_; 
v_k_x27_268_ = lean_array_fget_borrowed(v_ks_256_, v_x_253_);
v___x_269_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_254_, v_k_x27_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_271_; 
if (v_isShared_260_ == 0)
{
v___x_271_ = v___x_259_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_ks_256_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_vs_257_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_x_253_, v___x_272_);
lean_dec(v_x_253_);
v_x_252_ = v___x_271_;
v_x_253_ = v___x_273_;
goto _start;
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_array_fset(v_ks_256_, v_x_253_, v_x_254_);
v___x_277_ = lean_array_fset(v_vs_257_, v_x_253_, v_x_255_);
lean_dec(v_x_253_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_277_);
lean_ctor_set(v___x_259_, 0, v___x_276_);
v___x_279_ = v___x_259_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(lean_object* v_n_282_, lean_object* v_k_283_, lean_object* v_v_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(v_n_282_, v___x_285_, v_k_283_, v_v_284_);
return v___x_286_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0(void){
_start:
{
size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; 
v___x_287_ = ((size_t)5ULL);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_shift_left(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; 
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0);
v___x_292_ = lean_usize_sub(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(lean_object* v_x_294_, size_t v_x_295_, size_t v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v_es_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; lean_object* v_j_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_es_299_ = lean_ctor_get(v_x_294_, 0);
v___x_300_ = ((size_t)5ULL);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_303_ = lean_usize_land(v_x_295_, v___x_302_);
v_j_304_ = lean_usize_to_nat(v___x_303_);
v___x_305_ = lean_array_get_size(v_es_299_);
v___x_306_ = lean_nat_dec_lt(v_j_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v_j_304_);
lean_dec(v_x_298_);
lean_dec(v_x_297_);
return v_x_294_;
}
else
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_343_; 
lean_inc_ref(v_es_299_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_x_294_, 0);
lean_dec(v_unused_344_);
v___x_308_ = v_x_294_;
v_isShared_309_ = v_isSharedCheck_343_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_x_294_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_343_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_v_310_; lean_object* v___x_311_; lean_object* v_xs_x27_312_; lean_object* v___y_314_; 
v_v_310_ = lean_array_fget(v_es_299_, v_j_304_);
v___x_311_ = lean_box(0);
v_xs_x27_312_ = lean_array_fset(v_es_299_, v_j_304_, v___x_311_);
switch(lean_obj_tag(v_v_310_))
{
case 0:
{
lean_object* v_key_319_; lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_330_; 
v_key_319_ = lean_ctor_get(v_v_310_, 0);
v_val_320_ = lean_ctor_get(v_v_310_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_v_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_322_ = v_v_310_;
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_inc(v_key_319_);
lean_dec(v_v_310_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_330_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
uint8_t v___x_324_; 
v___x_324_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_297_, v_key_319_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_del_object(v___x_322_);
v___x_325_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_319_, v_val_320_, v_x_297_, v_x_298_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
else
{
lean_object* v___x_328_; 
lean_dec(v_val_320_);
lean_dec(v_key_319_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v_x_298_);
lean_ctor_set(v___x_322_, 0, v_x_297_);
v___x_328_ = v___x_322_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_x_297_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_x_298_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v___y_314_ = v___x_328_;
goto v___jp_313_;
}
}
}
}
case 1:
{
lean_object* v_node_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_341_; 
v_node_331_ = lean_ctor_get(v_v_310_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_v_310_);
if (v_isSharedCheck_341_ == 0)
{
v___x_333_ = v_v_310_;
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_node_331_);
lean_dec(v_v_310_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_341_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_335_ = lean_usize_shift_right(v_x_295_, v___x_300_);
v___x_336_ = lean_usize_add(v_x_296_, v___x_301_);
v___x_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_node_331_, v___x_335_, v___x_336_, v_x_297_, v_x_298_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_337_);
v___x_339_ = v___x_333_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v___y_314_ = v___x_339_;
goto v___jp_313_;
}
}
}
default: 
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_x_297_);
lean_ctor_set(v___x_342_, 1, v_x_298_);
v___y_314_ = v___x_342_;
goto v___jp_313_;
}
}
v___jp_313_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_array_fset(v_xs_x27_312_, v_j_304_, v___y_314_);
lean_dec(v_j_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_315_);
v___x_317_ = v___x_308_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v_ks_345_; lean_object* v_vs_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_366_; 
v_ks_345_ = lean_ctor_get(v_x_294_, 0);
v_vs_346_ = lean_ctor_get(v_x_294_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_366_ == 0)
{
v___x_348_ = v_x_294_;
v_isShared_349_ = v_isSharedCheck_366_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_vs_346_);
lean_inc(v_ks_345_);
lean_dec(v_x_294_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_366_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_ks_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_vs_346_);
v___x_351_ = v_reuseFailAlloc_365_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v_newNode_352_; uint8_t v___y_354_; size_t v___x_360_; uint8_t v___x_361_; 
v_newNode_352_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(v___x_351_, v_x_297_, v_x_298_);
v___x_360_ = ((size_t)7ULL);
v___x_361_ = lean_usize_dec_le(v___x_360_, v_x_296_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_352_);
v___x_363_ = lean_unsigned_to_nat(4u);
v___x_364_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
lean_dec(v___x_362_);
v___y_354_ = v___x_364_;
goto v___jp_353_;
}
else
{
v___y_354_ = v___x_361_;
goto v___jp_353_;
}
v___jp_353_:
{
if (v___y_354_ == 0)
{
lean_object* v_ks_355_; lean_object* v_vs_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_ks_355_ = lean_ctor_get(v_newNode_352_, 0);
lean_inc_ref(v_ks_355_);
v_vs_356_ = lean_ctor_get(v_newNode_352_, 1);
lean_inc_ref(v_vs_356_);
lean_dec_ref(v_newNode_352_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2);
v___x_359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_x_296_, v_ks_355_, v_vs_356_, v___x_357_, v___x_358_);
lean_dec_ref(v_vs_356_);
lean_dec_ref(v_ks_355_);
return v___x_359_;
}
else
{
return v_newNode_352_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(size_t v_depth_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_i_370_, lean_object* v_entries_371_){
_start:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_array_get_size(v_keys_368_);
v___x_373_ = lean_nat_dec_lt(v_i_370_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec(v_i_370_);
return v_entries_371_;
}
else
{
lean_object* v_k_374_; lean_object* v_v_375_; uint64_t v___x_376_; size_t v_h_377_; size_t v___x_378_; lean_object* v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v_h_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_k_374_ = lean_array_fget_borrowed(v_keys_368_, v_i_370_);
v_v_375_ = lean_array_fget_borrowed(v_vals_369_, v_i_370_);
v___x_376_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_374_);
v_h_377_ = lean_uint64_to_usize(v___x_376_);
v___x_378_ = ((size_t)5ULL);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v_depth_367_, v___x_380_);
v___x_382_ = lean_usize_mul(v___x_378_, v___x_381_);
v_h_383_ = lean_usize_shift_right(v_h_377_, v___x_382_);
v___x_384_ = lean_nat_add(v_i_370_, v___x_379_);
lean_dec(v_i_370_);
lean_inc(v_v_375_);
lean_inc(v_k_374_);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_entries_371_, v_h_383_, v_depth_367_, v_k_374_, v_v_375_);
v_i_370_ = v___x_384_;
v_entries_371_ = v___x_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_i_390_, lean_object* v_entries_391_){
_start:
{
size_t v_depth_boxed_392_; lean_object* v_res_393_; 
v_depth_boxed_392_ = lean_unbox_usize(v_depth_387_);
lean_dec(v_depth_387_);
v_res_393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_depth_boxed_392_, v_keys_388_, v_vals_389_, v_i_390_, v_entries_391_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
size_t v_x_2100__boxed_399_; size_t v_x_2101__boxed_400_; lean_object* v_res_401_; 
v_x_2100__boxed_399_ = lean_unbox_usize(v_x_395_);
lean_dec(v_x_395_);
v_x_2101__boxed_400_ = lean_unbox_usize(v_x_396_);
lean_dec(v_x_396_);
v_res_401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_394_, v_x_2100__boxed_399_, v_x_2101__boxed_400_, v_x_397_, v_x_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_405_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_403_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_402_, v___x_406_, v___x_407_, v_x_403_, v_x_404_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(lean_object* v_x_409_, lean_object* v_keys_410_, lean_object* v_v_411_, lean_object* v_k_412_, lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_c_416_; lean_object* v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_add(v_x_409_, v___x_414_);
v_c_416_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_410_, v_v_411_, v___x_415_);
lean_dec(v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_k_412_);
lean_ctor_set(v___x_417_, 1, v_c_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0___boxed(lean_object* v_x_418_, lean_object* v_keys_419_, lean_object* v_v_420_, lean_object* v_k_421_, lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_418_, v_keys_419_, v_v_420_, v_k_421_, v_x_422_);
lean_dec_ref(v_keys_419_);
lean_dec(v_x_418_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(lean_object* v_a_424_, lean_object* v_b_425_){
_start:
{
lean_object* v_fst_426_; lean_object* v_fst_427_; uint8_t v___x_428_; 
v_fst_426_ = lean_ctor_get(v_a_424_, 0);
v_fst_427_ = lean_ctor_get(v_b_425_, 0);
v___x_428_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_426_, v_fst_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1___boxed(lean_object* v_a_429_, lean_object* v_b_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_a_429_, v_b_430_);
lean_dec_ref(v_b_430_);
lean_dec_ref(v_a_429_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(lean_object* v_vs_433_, lean_object* v_v_434_, lean_object* v_i_435_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_array_get_size(v_vs_433_);
v___x_437_ = lean_nat_dec_lt(v_i_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_dec(v_i_435_);
v___x_438_ = lean_array_push(v_vs_433_, v_v_434_);
return v___x_438_;
}
else
{
lean_object* v_toCbvSimprocOLeanEntry_439_; lean_object* v_declName_440_; lean_object* v___x_441_; lean_object* v_toCbvSimprocOLeanEntry_442_; lean_object* v_declName_443_; uint8_t v___x_444_; 
v_toCbvSimprocOLeanEntry_439_ = lean_ctor_get(v_v_434_, 0);
v_declName_440_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_439_, 0);
v___x_441_ = lean_array_fget_borrowed(v_vs_433_, v_i_435_);
v_toCbvSimprocOLeanEntry_442_ = lean_ctor_get(v___x_441_, 0);
v_declName_443_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_442_, 0);
v___x_444_ = lean_name_eq(v_declName_440_, v_declName_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_i_435_, v___x_445_);
lean_dec(v_i_435_);
v_i_435_ = v___x_446_;
goto _start;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_array_fset(v_vs_433_, v_i_435_, v_v_434_);
lean_dec(v_i_435_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(lean_object* v_vs_449_, lean_object* v_v_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(v_vs_449_, v_v_450_, v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0));
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(lean_object* v_x_457_, lean_object* v_keys_458_, lean_object* v_v_459_, lean_object* v_k_460_, lean_object* v_as_461_, lean_object* v_k_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_mid_467_; lean_object* v_midVal_468_; uint8_t v___x_469_; 
v___x_465_ = lean_nat_add(v_x_463_, v_x_464_);
v___x_466_ = lean_unsigned_to_nat(1u);
v_mid_467_ = lean_nat_shiftr(v___x_465_, v___x_466_);
lean_dec(v___x_465_);
v_midVal_468_ = lean_array_fget(v_as_461_, v_mid_467_);
v___x_469_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_midVal_468_, v_k_462_);
if (v___x_469_ == 0)
{
uint8_t v___x_470_; 
lean_dec(v_x_464_);
v___x_470_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_462_, v_midVal_468_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
lean_dec(v_x_463_);
v___x_471_ = lean_array_get_size(v_as_461_);
v___x_472_ = lean_nat_dec_lt(v_mid_467_, v___x_471_);
if (v___x_472_ == 0)
{
lean_dec(v_midVal_468_);
lean_dec(v_mid_467_);
lean_dec(v_k_460_);
lean_dec_ref(v_v_459_);
return v_as_461_;
}
else
{
lean_object* v_snd_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_snd_473_ = lean_ctor_get(v_midVal_468_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_midVal_468_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_midVal_468_, 0);
lean_dec(v_unused_486_);
v___x_475_ = v_midVal_468_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snd_473_);
lean_dec(v_midVal_468_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v_xs_x27_478_; lean_object* v___x_479_; lean_object* v_c_480_; lean_object* v___x_482_; 
v___x_477_ = lean_box(0);
v_xs_x27_478_ = lean_array_fset(v_as_461_, v_mid_467_, v___x_477_);
v___x_479_ = lean_nat_add(v_x_457_, v___x_466_);
v_c_480_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_458_, v_v_459_, v___x_479_, v_snd_473_);
lean_dec(v___x_479_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_c_480_);
lean_ctor_set(v___x_475_, 0, v_k_460_);
v___x_482_ = v___x_475_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_c_480_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_array_fset(v_xs_x27_478_, v_mid_467_, v___x_482_);
lean_dec(v_mid_467_);
return v___x_483_;
}
}
}
}
else
{
lean_dec(v_midVal_468_);
v_x_464_ = v_mid_467_;
goto _start;
}
}
else
{
uint8_t v___x_488_; 
lean_dec(v_midVal_468_);
v___x_488_ = lean_nat_dec_eq(v_mid_467_, v_x_463_);
if (v___x_488_ == 0)
{
lean_dec(v_x_463_);
v_x_463_ = v_mid_467_;
goto _start;
}
else
{
lean_object* v___x_490_; lean_object* v_c_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_j_494_; lean_object* v_as_495_; lean_object* v___x_496_; 
lean_dec(v_mid_467_);
lean_dec(v_x_464_);
v___x_490_ = lean_nat_add(v_x_457_, v___x_466_);
v_c_491_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_458_, v_v_459_, v___x_490_);
lean_dec(v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_k_460_);
lean_ctor_set(v___x_492_, 1, v_c_491_);
v___x_493_ = lean_nat_add(v_x_463_, v___x_466_);
lean_dec(v_x_463_);
v_j_494_ = lean_array_get_size(v_as_461_);
v_as_495_ = lean_array_push(v_as_461_, v___x_492_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_493_, v_as_495_, v_j_494_);
lean_dec(v___x_493_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(lean_object* v_x_497_, lean_object* v_keys_498_, lean_object* v_v_499_, lean_object* v_k_500_, lean_object* v_as_501_, lean_object* v_k_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_array_get_size(v_as_501_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_array_fget_borrowed(v_as_501_, v___x_504_);
v___x_507_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_502_, v___x_506_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v___x_506_, v_k_502_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_lt(v___x_504_, v___x_503_);
if (v___x_509_ == 0)
{
lean_dec(v_k_500_);
lean_dec_ref(v_v_499_);
return v_as_501_;
}
else
{
lean_object* v___x_510_; lean_object* v_xs_x27_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_inc(v___x_506_);
v___x_510_ = lean_box(0);
v_xs_x27_511_ = lean_array_fset(v_as_501_, v___x_504_, v___x_510_);
v___x_512_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_506_);
v___x_513_ = lean_array_fset(v_xs_x27_511_, v___x_504_, v___x_512_);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_sub(v___x_503_, v___x_514_);
v___x_516_ = lean_array_fget_borrowed(v_as_501_, v___x_515_);
v___x_517_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v___x_516_, v_k_502_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; 
v___x_518_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_502_, v___x_516_);
if (v___x_518_ == 0)
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_lt(v___x_515_, v___x_503_);
if (v___x_519_ == 0)
{
lean_dec(v___x_515_);
lean_dec(v_k_500_);
lean_dec_ref(v_v_499_);
return v_as_501_;
}
else
{
lean_object* v___x_520_; lean_object* v_xs_x27_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc(v___x_516_);
v___x_520_ = lean_box(0);
v_xs_x27_521_ = lean_array_fset(v_as_501_, v___x_515_, v___x_520_);
v___x_522_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_516_);
v___x_523_ = lean_array_fset(v_xs_x27_521_, v___x_515_, v___x_522_);
lean_dec(v___x_515_);
return v___x_523_;
}
}
else
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v_as_501_, v_k_502_, v___x_504_, v___x_515_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_515_);
v___x_525_ = lean_box(0);
v___x_526_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_525_);
v___x_527_ = lean_array_push(v_as_501_, v___x_526_);
return v___x_527_;
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_as_530_; lean_object* v___x_531_; 
v___x_528_ = lean_box(0);
v___x_529_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_528_);
v_as_530_ = lean_array_push(v_as_501_, v___x_529_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_504_, v_as_530_, v___x_503_);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_box(0);
v___x_533_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_497_, v_keys_498_, v_v_499_, v_k_500_, v___x_532_);
v___x_534_ = lean_array_push(v_as_501_, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(lean_object* v_keys_535_, lean_object* v_v_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_vs_539_; lean_object* v_children_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_557_; 
v_vs_539_ = lean_ctor_get(v_x_538_, 0);
v_children_540_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_557_ == 0)
{
v___x_542_ = v_x_538_;
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_children_540_);
lean_inc(v_vs_539_);
lean_dec(v_x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_array_get_size(v_keys_535_);
v___x_545_ = lean_nat_dec_lt(v_x_537_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(v_vs_539_, v_v_536_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_546_);
v___x_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_children_540_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_object* v_k_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_c_553_; lean_object* v___x_555_; 
v_k_550_ = lean_array_fget_borrowed(v_keys_535_, v_x_537_);
v___x_551_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1);
lean_inc(v_k_550_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v_k_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
lean_inc(v_k_550_);
v_c_553_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(v_x_537_, v_keys_535_, v_v_536_, v_k_550_, v_children_540_, v___x_552_);
lean_dec_ref(v___x_552_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_c_553_);
v___x_555_ = v___x_542_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_vs_539_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_c_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(lean_object* v_x_558_, lean_object* v_keys_559_, lean_object* v_v_560_, lean_object* v_k_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_snd_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_573_; 
v_snd_563_ = lean_ctor_get(v_x_562_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_x_562_, 0);
lean_dec(v_unused_574_);
v___x_565_ = v_x_562_;
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snd_563_);
lean_dec(v_x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_c_569_; lean_object* v___x_571_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_x_558_, v___x_567_);
v_c_569_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_559_, v_v_560_, v___x_568_, v_snd_563_);
lean_dec(v___x_568_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_c_569_);
lean_ctor_set(v___x_565_, 0, v_k_561_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_k_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_c_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2___boxed(lean_object* v_x_575_, lean_object* v_keys_576_, lean_object* v_v_577_, lean_object* v_k_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_575_, v_keys_576_, v_v_577_, v_k_578_, v_x_579_);
lean_dec_ref(v_keys_576_);
lean_dec(v_x_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___boxed(lean_object* v_keys_581_, lean_object* v_v_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_581_, v_v_582_, v_x_583_, v_x_584_);
lean_dec(v_x_583_);
lean_dec_ref(v_keys_581_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg___boxed(lean_object* v_x_586_, lean_object* v_keys_587_, lean_object* v_v_588_, lean_object* v_k_589_, lean_object* v_as_590_, lean_object* v_k_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_586_, v_keys_587_, v_v_588_, v_k_589_, v_as_590_, v_k_591_, v_x_592_, v_x_593_);
lean_dec_ref(v_k_591_);
lean_dec_ref(v_keys_587_);
lean_dec(v_x_586_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___boxed(lean_object* v_x_595_, lean_object* v_keys_596_, lean_object* v_v_597_, lean_object* v_k_598_, lean_object* v_as_599_, lean_object* v_k_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(v_x_595_, v_keys_596_, v_v_597_, v_k_598_, v_as_599_, v_k_600_);
lean_dec_ref(v_k_600_);
lean_dec_ref(v_keys_596_);
lean_dec(v_x_595_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(lean_object* v_keys_602_, lean_object* v_vals_603_, lean_object* v_i_604_, lean_object* v_k_605_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_array_get_size(v_keys_602_);
v___x_607_ = lean_nat_dec_lt(v_i_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec(v_i_604_);
v___x_608_ = lean_box(0);
return v___x_608_;
}
else
{
lean_object* v_k_x27_609_; uint8_t v___x_610_; 
v_k_x27_609_ = lean_array_fget_borrowed(v_keys_602_, v_i_604_);
v___x_610_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_605_, v_k_x27_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_i_604_, v___x_611_);
lean_dec(v_i_604_);
v_i_604_ = v___x_612_;
goto _start;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_array_fget_borrowed(v_vals_603_, v_i_604_);
lean_dec(v_i_604_);
lean_inc(v___x_614_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_keys_616_, lean_object* v_vals_617_, lean_object* v_i_618_, lean_object* v_k_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_keys_616_, v_vals_617_, v_i_618_, v_k_619_);
lean_dec(v_k_619_);
lean_dec_ref(v_vals_617_);
lean_dec_ref(v_keys_616_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(lean_object* v_x_621_, size_t v_x_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v_es_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_645_; 
v_es_624_ = lean_ctor_get(v_x_621_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_645_ == 0)
{
v___x_626_ = v_x_621_;
v_isShared_627_ = v_isSharedCheck_645_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_es_624_);
lean_dec(v_x_621_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_645_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v_j_632_; lean_object* v___x_633_; 
v___x_628_ = lean_box(2);
v___x_629_ = ((size_t)5ULL);
v___x_630_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_631_ = lean_usize_land(v_x_622_, v___x_630_);
v_j_632_ = lean_usize_to_nat(v___x_631_);
v___x_633_ = lean_array_get(v___x_628_, v_es_624_, v_j_632_);
lean_dec(v_j_632_);
lean_dec_ref(v_es_624_);
switch(lean_obj_tag(v___x_633_))
{
case 0:
{
lean_object* v_key_634_; lean_object* v_val_635_; uint8_t v___x_636_; 
v_key_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_key_634_);
v_val_635_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_val_635_);
lean_dec_ref(v___x_633_);
v___x_636_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_623_, v_key_634_);
lean_dec(v_key_634_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v_val_635_);
lean_del_object(v___x_626_);
v___x_637_ = lean_box(0);
return v___x_637_;
}
else
{
lean_object* v___x_639_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 1);
lean_ctor_set(v___x_626_, 0, v_val_635_);
v___x_639_ = v___x_626_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_val_635_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
case 1:
{
lean_object* v_node_641_; size_t v___x_642_; 
lean_del_object(v___x_626_);
v_node_641_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_node_641_);
lean_dec_ref(v___x_633_);
v___x_642_ = lean_usize_shift_right(v_x_622_, v___x_629_);
v_x_621_ = v_node_641_;
v_x_622_ = v___x_642_;
goto _start;
}
default: 
{
lean_object* v___x_644_; 
lean_del_object(v___x_626_);
v___x_644_ = lean_box(0);
return v___x_644_;
}
}
}
}
else
{
lean_object* v_ks_646_; lean_object* v_vs_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_ks_646_ = lean_ctor_get(v_x_621_, 0);
lean_inc_ref(v_ks_646_);
v_vs_647_ = lean_ctor_get(v_x_621_, 1);
lean_inc_ref(v_vs_647_);
lean_dec_ref(v_x_621_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_ks_646_, v_vs_647_, v___x_648_, v_x_623_);
lean_dec_ref(v_vs_647_);
lean_dec_ref(v_ks_646_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
size_t v_x_2540__boxed_653_; lean_object* v_res_654_; 
v_x_2540__boxed_653_ = lean_unbox_usize(v_x_651_);
lean_dec(v_x_651_);
v_res_654_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_650_, v_x_2540__boxed_653_, v_x_652_);
lean_dec(v_x_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
uint64_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_656_);
v___x_658_ = lean_uint64_to_usize(v___x_657_);
v___x_659_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_655_, v___x_658_, v_x_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_x_660_, v_x_661_);
lean_dec(v_x_661_);
return v_res_662_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_666_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2));
v___x_667_ = lean_unsigned_to_nat(23u);
v___x_668_ = lean_unsigned_to_nat(166u);
v___x_669_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1));
v___x_670_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0));
v___x_671_ = l_mkPanicMessageWithDecl(v___x_670_, v___x_669_, v___x_668_, v___x_667_, v___x_666_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(lean_object* v_d_672_, lean_object* v_keys_673_, lean_object* v_v_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_array_get_size(v_keys_673_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_nat_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v_k_679_; lean_object* v___x_680_; 
v___x_678_ = lean_box(0);
v_k_679_ = lean_array_get_borrowed(v___x_678_, v_keys_673_, v___x_676_);
lean_inc_ref(v_d_672_);
v___x_680_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_d_672_, v_k_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v_c_682_; lean_object* v___x_683_; 
v___x_681_ = lean_unsigned_to_nat(1u);
v_c_682_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_673_, v_v_674_, v___x_681_);
lean_inc(v_k_679_);
v___x_683_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_d_672_, v_k_679_, v_c_682_);
return v___x_683_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_685_; lean_object* v_c_686_; lean_object* v___x_687_; 
v_val_684_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v___x_680_);
v___x_685_ = lean_unsigned_to_nat(1u);
v_c_686_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_673_, v_v_674_, v___x_685_, v_val_684_);
lean_inc(v_k_679_);
v___x_687_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_d_672_, v_k_679_, v_c_686_);
return v___x_687_;
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec_ref(v_v_674_);
lean_dec_ref(v_d_672_);
v___x_688_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3);
v___x_689_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(lean_object* v_d_690_, lean_object* v_keys_691_, lean_object* v_v_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_d_690_, v_keys_691_, v_v_692_);
lean_dec_ref(v_keys_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v_ks_698_; lean_object* v_vs_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_723_; 
v_ks_698_ = lean_ctor_get(v_x_694_, 0);
v_vs_699_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_723_ == 0)
{
v___x_701_ = v_x_694_;
v_isShared_702_ = v_isSharedCheck_723_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_vs_699_);
lean_inc(v_ks_698_);
lean_dec(v_x_694_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_723_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_array_get_size(v_ks_698_);
v___x_704_ = lean_nat_dec_lt(v_x_695_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
lean_dec(v_x_695_);
v___x_705_ = lean_array_push(v_ks_698_, v_x_696_);
v___x_706_ = lean_array_push(v_vs_699_, v_x_697_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_706_);
lean_ctor_set(v___x_701_, 0, v___x_705_);
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v_k_x27_710_; uint8_t v___x_711_; 
v_k_x27_710_ = lean_array_fget_borrowed(v_ks_698_, v_x_695_);
v___x_711_ = lean_name_eq(v_x_696_, v_k_x27_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_713_; 
if (v_isShared_702_ == 0)
{
v___x_713_ = v___x_701_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_ks_698_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_vs_699_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_nat_add(v_x_695_, v___x_714_);
lean_dec(v_x_695_);
v_x_694_ = v___x_713_;
v_x_695_ = v___x_715_;
goto _start;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = lean_array_fset(v_ks_698_, v_x_695_, v_x_696_);
v___x_719_ = lean_array_fset(v_vs_699_, v_x_695_, v_x_697_);
lean_dec(v_x_695_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_719_);
lean_ctor_set(v___x_701_, 0, v___x_718_);
v___x_721_ = v___x_701_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_724_, lean_object* v_k_725_, lean_object* v_v_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_n_724_, v___x_727_, v_k_725_, v_v_726_);
return v___x_728_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_729_; uint64_t v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(1723u);
v___x_730_ = lean_uint64_of_nat(v___x_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(lean_object* v_x_732_, size_t v_x_733_, size_t v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
lean_object* v_es_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; lean_object* v_j_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_es_737_ = lean_ctor_get(v_x_732_, 0);
v___x_738_ = ((size_t)5ULL);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_741_ = lean_usize_land(v_x_733_, v___x_740_);
v_j_742_ = lean_usize_to_nat(v___x_741_);
v___x_743_ = lean_array_get_size(v_es_737_);
v___x_744_ = lean_nat_dec_lt(v_j_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v_j_742_);
lean_dec(v_x_736_);
lean_dec(v_x_735_);
return v_x_732_;
}
else
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_781_; 
lean_inc_ref(v_es_737_);
v_isSharedCheck_781_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_x_732_, 0);
lean_dec(v_unused_782_);
v___x_746_ = v_x_732_;
v_isShared_747_ = v_isSharedCheck_781_;
goto v_resetjp_745_;
}
else
{
lean_dec(v_x_732_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_781_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_v_748_; lean_object* v___x_749_; lean_object* v_xs_x27_750_; lean_object* v___y_752_; 
v_v_748_ = lean_array_fget(v_es_737_, v_j_742_);
v___x_749_ = lean_box(0);
v_xs_x27_750_ = lean_array_fset(v_es_737_, v_j_742_, v___x_749_);
switch(lean_obj_tag(v_v_748_))
{
case 0:
{
lean_object* v_key_757_; lean_object* v_val_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_768_; 
v_key_757_ = lean_ctor_get(v_v_748_, 0);
v_val_758_ = lean_ctor_get(v_v_748_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_v_748_);
if (v_isSharedCheck_768_ == 0)
{
v___x_760_ = v_v_748_;
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_val_758_);
lean_inc(v_key_757_);
lean_dec(v_v_748_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
uint8_t v___x_762_; 
v___x_762_ = lean_name_eq(v_x_735_, v_key_757_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_del_object(v___x_760_);
v___x_763_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_757_, v_val_758_, v_x_735_, v_x_736_);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
v___y_752_ = v___x_764_;
goto v___jp_751_;
}
else
{
lean_object* v___x_766_; 
lean_dec(v_val_758_);
lean_dec(v_key_757_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_x_736_);
lean_ctor_set(v___x_760_, 0, v_x_735_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_x_735_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_x_736_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
v___y_752_ = v___x_766_;
goto v___jp_751_;
}
}
}
}
case 1:
{
lean_object* v_node_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_779_; 
v_node_769_ = lean_ctor_get(v_v_748_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_v_748_);
if (v_isSharedCheck_779_ == 0)
{
v___x_771_ = v_v_748_;
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_node_769_);
lean_dec(v_v_748_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_779_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_773_ = lean_usize_shift_right(v_x_733_, v___x_738_);
v___x_774_ = lean_usize_add(v_x_734_, v___x_739_);
v___x_775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_node_769_, v___x_773_, v___x_774_, v_x_735_, v_x_736_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_777_ = v___x_771_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
v___y_752_ = v___x_777_;
goto v___jp_751_;
}
}
}
default: 
{
lean_object* v___x_780_; 
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_x_735_);
lean_ctor_set(v___x_780_, 1, v_x_736_);
v___y_752_ = v___x_780_;
goto v___jp_751_;
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_array_fset(v_xs_x27_750_, v_j_742_, v___y_752_);
lean_dec(v_j_742_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_753_);
v___x_755_ = v___x_746_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_object* v_ks_783_; lean_object* v_vs_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_804_; 
v_ks_783_ = lean_ctor_get(v_x_732_, 0);
v_vs_784_ = lean_ctor_get(v_x_732_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_732_);
if (v_isSharedCheck_804_ == 0)
{
v___x_786_ = v_x_732_;
v_isShared_787_ = v_isSharedCheck_804_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_vs_784_);
lean_inc(v_ks_783_);
lean_dec(v_x_732_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_804_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_ks_783_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_vs_784_);
v___x_789_ = v_reuseFailAlloc_803_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v_newNode_790_; uint8_t v___y_792_; size_t v___x_798_; uint8_t v___x_799_; 
v_newNode_790_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v___x_789_, v_x_735_, v_x_736_);
v___x_798_ = ((size_t)7ULL);
v___x_799_ = lean_usize_dec_le(v___x_798_, v_x_734_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_790_);
v___x_801_ = lean_unsigned_to_nat(4u);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
lean_dec(v___x_800_);
v___y_792_ = v___x_802_;
goto v___jp_791_;
}
else
{
v___y_792_ = v___x_799_;
goto v___jp_791_;
}
v___jp_791_:
{
if (v___y_792_ == 0)
{
lean_object* v_ks_793_; lean_object* v_vs_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_ks_793_ = lean_ctor_get(v_newNode_790_, 0);
lean_inc_ref(v_ks_793_);
v_vs_794_ = lean_ctor_get(v_newNode_790_, 1);
lean_inc_ref(v_vs_794_);
lean_dec_ref(v_newNode_790_);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0);
v___x_797_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_x_734_, v_ks_793_, v_vs_794_, v___x_795_, v___x_796_);
lean_dec_ref(v_vs_794_);
lean_dec_ref(v_ks_793_);
return v___x_797_;
}
else
{
return v_newNode_790_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_805_, lean_object* v_keys_806_, lean_object* v_vals_807_, lean_object* v_i_808_, lean_object* v_entries_809_){
_start:
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = lean_array_get_size(v_keys_806_);
v___x_811_ = lean_nat_dec_lt(v_i_808_, v___x_810_);
if (v___x_811_ == 0)
{
lean_dec(v_i_808_);
return v_entries_809_;
}
else
{
lean_object* v_k_812_; lean_object* v_v_813_; uint64_t v___y_815_; 
v_k_812_ = lean_array_fget_borrowed(v_keys_806_, v_i_808_);
v_v_813_ = lean_array_fget_borrowed(v_vals_807_, v_i_808_);
if (lean_obj_tag(v_k_812_) == 0)
{
uint64_t v___x_826_; 
v___x_826_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_815_ = v___x_826_;
goto v___jp_814_;
}
else
{
uint64_t v_hash_827_; 
v_hash_827_ = lean_ctor_get_uint64(v_k_812_, sizeof(void*)*2);
v___y_815_ = v_hash_827_;
goto v___jp_814_;
}
v___jp_814_:
{
size_t v_h_816_; size_t v___x_817_; lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v_h_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_h_816_ = lean_uint64_to_usize(v___y_815_);
v___x_817_ = ((size_t)5ULL);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_sub(v_depth_805_, v___x_819_);
v___x_821_ = lean_usize_mul(v___x_817_, v___x_820_);
v_h_822_ = lean_usize_shift_right(v_h_816_, v___x_821_);
v___x_823_ = lean_nat_add(v_i_808_, v___x_818_);
lean_dec(v_i_808_);
lean_inc(v_v_813_);
lean_inc(v_k_812_);
v___x_824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_entries_809_, v_h_822_, v_depth_805_, v_k_812_, v_v_813_);
v_i_808_ = v___x_823_;
v_entries_809_ = v___x_824_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_828_, lean_object* v_keys_829_, lean_object* v_vals_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
size_t v_depth_boxed_833_; lean_object* v_res_834_; 
v_depth_boxed_833_ = lean_unbox_usize(v_depth_828_);
lean_dec(v_depth_828_);
v_res_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_833_, v_keys_829_, v_vals_830_, v_i_831_, v_entries_832_);
lean_dec_ref(v_vals_830_);
lean_dec_ref(v_keys_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_2752__boxed_840_; size_t v_x_2753__boxed_841_; lean_object* v_res_842_; 
v_x_2752__boxed_840_ = lean_unbox_usize(v_x_836_);
lean_dec(v_x_836_);
v_x_2753__boxed_841_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_835_, v_x_2752__boxed_840_, v_x_2753__boxed_841_, v_x_838_, v_x_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
uint64_t v___y_847_; 
if (lean_obj_tag(v_x_844_) == 0)
{
uint64_t v___x_851_; 
v___x_851_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_847_ = v___x_851_;
goto v___jp_846_;
}
else
{
uint64_t v_hash_852_; 
v_hash_852_ = lean_ctor_get_uint64(v_x_844_, sizeof(void*)*2);
v___y_847_ = v_hash_852_;
goto v___jp_846_;
}
v___jp_846_:
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_uint64_to_usize(v___y_847_);
v___x_849_ = ((size_t)1ULL);
v___x_850_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_843_, v___x_848_, v___x_849_, v_x_844_, v_x_845_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(lean_object* v_xs_853_, lean_object* v_v_854_, lean_object* v_i_855_){
_start:
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_array_get_size(v_xs_853_);
v___x_857_ = lean_nat_dec_lt(v_i_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_dec(v_i_855_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
else
{
lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_array_fget_borrowed(v_xs_853_, v_i_855_);
v___x_860_ = lean_name_eq(v___x_859_, v_v_854_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v_i_855_, v___x_861_);
lean_dec(v_i_855_);
v_i_855_ = v___x_862_;
goto _start;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v_i_855_);
return v___x_864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_xs_865_, lean_object* v_v_866_, lean_object* v_i_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_865_, v_v_866_, v_i_867_);
lean_dec(v_v_866_);
lean_dec_ref(v_xs_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(lean_object* v_xs_869_, lean_object* v_v_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_869_, v_v_870_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(lean_object* v_xs_873_, lean_object* v_v_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_xs_873_, v_v_874_);
lean_dec(v_v_874_);
lean_dec_ref(v_xs_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(lean_object* v_x_876_, size_t v_x_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_876_) == 0)
{
lean_object* v_es_879_; lean_object* v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; lean_object* v_j_884_; lean_object* v_entry_885_; 
v_es_879_ = lean_ctor_get(v_x_876_, 0);
v___x_880_ = lean_box(2);
v___x_881_ = ((size_t)5ULL);
v___x_882_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_883_ = lean_usize_land(v_x_877_, v___x_882_);
v_j_884_ = lean_usize_to_nat(v___x_883_);
v_entry_885_ = lean_array_get(v___x_880_, v_es_879_, v_j_884_);
switch(lean_obj_tag(v_entry_885_))
{
case 0:
{
lean_object* v_key_886_; uint8_t v___x_887_; 
v_key_886_ = lean_ctor_get(v_entry_885_, 0);
lean_inc(v_key_886_);
lean_dec_ref(v_entry_885_);
v___x_887_ = lean_name_eq(v_x_878_, v_key_886_);
lean_dec(v_key_886_);
if (v___x_887_ == 0)
{
lean_dec(v_j_884_);
return v_x_876_;
}
else
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_895_; 
lean_inc_ref(v_es_879_);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_x_876_, 0);
lean_dec(v_unused_896_);
v___x_889_ = v_x_876_;
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_x_876_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_array_set(v_es_879_, v_j_884_, v___x_880_);
lean_dec(v_j_884_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
case 1:
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_930_; 
lean_inc_ref(v_es_879_);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_x_876_, 0);
lean_dec(v_unused_931_);
v___x_898_ = v_x_876_;
v_isShared_899_ = v_isSharedCheck_930_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_x_876_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_930_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_node_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_929_; 
v_node_900_ = lean_ctor_get(v_entry_885_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_entry_885_);
if (v_isSharedCheck_929_ == 0)
{
v___x_902_ = v_entry_885_;
v_isShared_903_ = v_isSharedCheck_929_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_node_900_);
lean_dec(v_entry_885_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_929_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_entries_904_; size_t v___x_905_; lean_object* v_newNode_906_; lean_object* v___x_907_; 
v_entries_904_ = lean_array_set(v_es_879_, v_j_884_, v___x_880_);
v___x_905_ = lean_usize_shift_right(v_x_877_, v___x_881_);
v_newNode_906_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_node_900_, v___x_905_, v_x_878_);
lean_inc_ref(v_newNode_906_);
v___x_907_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_909_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v_newNode_906_);
v___x_909_ = v___x_902_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_newNode_906_);
v___x_909_ = v_reuseFailAlloc_914_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_910_ = lean_array_set(v_entries_904_, v_j_884_, v___x_909_);
lean_dec(v_j_884_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_910_);
v___x_912_ = v___x_898_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_val_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_newNode_906_);
lean_del_object(v___x_902_);
v_val_915_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_val_915_);
lean_dec_ref(v___x_907_);
v_fst_916_ = lean_ctor_get(v_val_915_, 0);
v_snd_917_ = lean_ctor_get(v_val_915_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_val_915_);
if (v_isSharedCheck_928_ == 0)
{
v___x_919_ = v_val_915_;
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_snd_917_);
lean_inc(v_fst_916_);
lean_dec(v_val_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_928_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_fst_916_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_snd_917_);
v___x_922_ = v_reuseFailAlloc_927_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_array_set(v_entries_904_, v_j_884_, v___x_922_);
lean_dec(v_j_884_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_923_);
v___x_925_ = v___x_898_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_884_);
return v_x_876_;
}
}
}
else
{
lean_object* v_ks_932_; lean_object* v_vs_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_ks_932_ = lean_ctor_get(v_x_876_, 0);
v_vs_933_ = lean_ctor_get(v_x_876_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_x_876_);
if (v_isSharedCheck_947_ == 0)
{
v___x_935_ = v_x_876_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_vs_933_);
lean_inc(v_ks_932_);
lean_dec(v_x_876_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; 
v___x_937_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_ks_932_, v_x_878_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_939_; 
if (v_isShared_936_ == 0)
{
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_ks_932_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_vs_933_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
else
{
lean_object* v_val_941_; lean_object* v_keys_x27_942_; lean_object* v_vals_x27_943_; lean_object* v___x_945_; 
v_val_941_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_val_941_);
lean_dec_ref(v___x_937_);
lean_inc(v_val_941_);
v_keys_x27_942_ = l_Array_eraseIdx___redArg(v_ks_932_, v_val_941_);
v_vals_x27_943_ = l_Array_eraseIdx___redArg(v_vs_933_, v_val_941_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v_vals_x27_943_);
lean_ctor_set(v___x_935_, 0, v_keys_x27_942_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_keys_x27_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_vals_x27_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v_x_2961__boxed_951_; lean_object* v_res_952_; 
v_x_2961__boxed_951_ = lean_unbox_usize(v_x_949_);
lean_dec(v_x_949_);
v_res_952_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_948_, v_x_2961__boxed_951_, v_x_950_);
lean_dec(v_x_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
uint64_t v___y_956_; 
if (lean_obj_tag(v_x_954_) == 0)
{
uint64_t v___x_959_; 
v___x_959_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_956_ = v___x_959_;
goto v___jp_955_;
}
else
{
uint64_t v_hash_960_; 
v_hash_960_ = lean_ctor_get_uint64(v_x_954_, sizeof(void*)*2);
v___y_956_ = v_hash_960_;
goto v___jp_955_;
}
v___jp_955_:
{
size_t v_h_957_; lean_object* v___x_958_; 
v_h_957_ = lean_uint64_to_usize(v___y_956_);
v___x_958_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_953_, v_h_957_, v_x_954_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_961_, v_x_962_);
lean_dec(v_x_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(lean_object* v_s_964_, lean_object* v_keys_965_, lean_object* v_declName_966_, uint8_t v_phase_967_, lean_object* v_proc_968_){
_start:
{
lean_object* v_pre_969_; lean_object* v_eval_970_; lean_object* v_post_971_; lean_object* v_simprocNames_972_; lean_object* v_erased_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_994_; 
v_pre_969_ = lean_ctor_get(v_s_964_, 0);
v_eval_970_ = lean_ctor_get(v_s_964_, 1);
v_post_971_ = lean_ctor_get(v_s_964_, 2);
v_simprocNames_972_ = lean_ctor_get(v_s_964_, 3);
v_erased_973_ = lean_ctor_get(v_s_964_, 4);
v_isSharedCheck_994_ = !lean_is_exclusive(v_s_964_);
if (v_isSharedCheck_994_ == 0)
{
v___x_975_ = v_s_964_;
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_erased_973_);
lean_inc(v_simprocNames_972_);
lean_inc(v_post_971_);
lean_inc(v_eval_970_);
lean_inc(v_pre_969_);
lean_dec(v_s_964_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_994_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v_entry_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_inc_ref(v_keys_965_);
lean_inc(v_declName_966_);
v___x_977_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_977_, 0, v_declName_966_);
lean_ctor_set(v___x_977_, 1, v_keys_965_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*2, v_phase_967_);
v_entry_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_entry_978_, 0, v___x_977_);
lean_ctor_set(v_entry_978_, 1, v_proc_968_);
v___x_979_ = lean_box(0);
lean_inc(v_declName_966_);
v___x_980_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_simprocNames_972_, v_declName_966_, v___x_979_);
v___x_981_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_erased_973_, v_declName_966_);
lean_dec(v_declName_966_);
switch(v_phase_967_)
{
case 0:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_pre_969_, v_keys_965_, v_entry_978_);
lean_dec_ref(v_keys_965_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 4, v___x_981_);
lean_ctor_set(v___x_975_, 3, v___x_980_);
lean_ctor_set(v___x_975_, 0, v___x_982_);
v___x_984_ = v___x_975_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_eval_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_post_971_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v___x_981_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
case 1:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_eval_970_, v_keys_965_, v_entry_978_);
lean_dec_ref(v_keys_965_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 4, v___x_981_);
lean_ctor_set(v___x_975_, 3, v___x_980_);
lean_ctor_set(v___x_975_, 1, v___x_986_);
v___x_988_ = v___x_975_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_pre_969_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_post_971_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v___x_981_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
default: 
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_post_971_, v_keys_965_, v_entry_978_);
lean_dec_ref(v_keys_965_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 4, v___x_981_);
lean_ctor_set(v___x_975_, 3, v___x_980_);
lean_ctor_set(v___x_975_, 2, v___x_990_);
v___x_992_ = v___x_975_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_pre_969_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_eval_970_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v___x_981_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(lean_object* v_s_995_, lean_object* v_keys_996_, lean_object* v_declName_997_, lean_object* v_phase_998_, lean_object* v_proc_999_){
_start:
{
uint8_t v_phase_boxed_1000_; lean_object* v_res_1001_; 
v_phase_boxed_1000_ = lean_unbox(v_phase_998_);
v_res_1001_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_995_, v_keys_996_, v_declName_997_, v_phase_boxed_1000_, v_proc_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(lean_object* v_00_u03b2_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_x_1003_, v_x_1004_, v_x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_1008_, v_x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(lean_object* v_00_u03b2_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(v_00_u03b2_1011_, v_x_1012_, v_x_1013_);
lean_dec(v_x_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(lean_object* v_00_u03b2_1015_, lean_object* v_x_1016_, size_t v_x_1017_, size_t v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_1016_, v_x_1017_, v_x_1018_, v_x_1019_, v_x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
size_t v_x_3172__boxed_1028_; size_t v_x_3173__boxed_1029_; lean_object* v_res_1030_; 
v_x_3172__boxed_1028_ = lean_unbox_usize(v_x_1024_);
lean_dec(v_x_1024_);
v_x_3173__boxed_1029_ = lean_unbox_usize(v_x_1025_);
lean_dec(v_x_1025_);
v_res_1030_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(v_00_u03b2_1022_, v_x_1023_, v_x_3172__boxed_1028_, v_x_3173__boxed_1029_, v_x_1026_, v_x_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(lean_object* v_00_u03b2_1031_, lean_object* v_x_1032_, size_t v_x_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_1032_, v_x_1033_, v_x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
size_t v_x_3189__boxed_1040_; lean_object* v_res_1041_; 
v_x_3189__boxed_1040_ = lean_unbox_usize(v_x_1038_);
lean_dec(v_x_1038_);
v_res_1041_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(v_00_u03b2_1036_, v_x_1037_, v_x_3189__boxed_1040_, v_x_1039_);
lean_dec(v_x_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_x_1043_, v_x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_00_u03b2_1046_, v_x_1047_, v_x_1048_);
lean_dec(v_x_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_x_1051_, v_x_1052_, v_x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1055_, lean_object* v_n_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v_n_1056_, v_k_1057_, v_v_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1060_, size_t v_depth_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_entries_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_1061_, v_keys_1062_, v_vals_1063_, v_i_1065_, v_entries_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_heq_1072_, lean_object* v_i_1073_, lean_object* v_entries_1074_){
_start:
{
size_t v_depth_boxed_1075_; lean_object* v_res_1076_; 
v_depth_boxed_1075_ = lean_unbox_usize(v_depth_1069_);
lean_dec(v_depth_1069_);
v_res_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(v_00_u03b2_1068_, v_depth_boxed_1075_, v_keys_1070_, v_vals_1071_, v_heq_1072_, v_i_1073_, v_entries_1074_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, size_t v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
size_t v_x_3220__boxed_1086_; lean_object* v_res_1087_; 
v_x_3220__boxed_1086_ = lean_unbox_usize(v_x_1084_);
lean_dec(v_x_1084_);
v_res_1087_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v_00_u03b2_1082_, v_x_1083_, v_x_3220__boxed_1086_, v_x_1085_);
lean_dec(v_x_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, size_t v_x_1090_, size_t v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_1089_, v_x_1090_, v_x_1091_, v_x_1092_, v_x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___boxed(lean_object* v_00_u03b2_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
size_t v_x_3231__boxed_1101_; size_t v_x_3232__boxed_1102_; lean_object* v_res_1103_; 
v_x_3231__boxed_1101_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_x_3232__boxed_1102_ = lean_unbox_usize(v_x_1098_);
lean_dec(v_x_1098_);
v_res_1103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(v_00_u03b2_1095_, v_x_1096_, v_x_3231__boxed_1101_, v_x_3232__boxed_1102_, v_x_1099_, v_x_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1105_, v_x_1106_, v_x_1107_, v_x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1110_, lean_object* v_keys_1111_, lean_object* v_vals_1112_, lean_object* v_heq_1113_, lean_object* v_i_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_keys_1111_, v_vals_1112_, v_i_1114_, v_k_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_keys_1118_, lean_object* v_vals_1119_, lean_object* v_heq_1120_, lean_object* v_i_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(v_00_u03b2_1117_, v_keys_1118_, v_vals_1119_, v_heq_1120_, v_i_1121_, v_k_1122_);
lean_dec(v_k_1122_);
lean_dec_ref(v_vals_1119_);
lean_dec_ref(v_keys_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15(lean_object* v_00_u03b2_1124_, lean_object* v_n_1125_, lean_object* v_k_1126_, lean_object* v_v_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(v_n_1125_, v_k_1126_, v_v_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_1129_, size_t v_depth_1130_, lean_object* v_keys_1131_, lean_object* v_vals_1132_, lean_object* v_heq_1133_, lean_object* v_i_1134_, lean_object* v_entries_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_depth_1130_, v_keys_1131_, v_vals_1132_, v_i_1134_, v_entries_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_1137_, lean_object* v_depth_1138_, lean_object* v_keys_1139_, lean_object* v_vals_1140_, lean_object* v_heq_1141_, lean_object* v_i_1142_, lean_object* v_entries_1143_){
_start:
{
size_t v_depth_boxed_1144_; lean_object* v_res_1145_; 
v_depth_boxed_1144_ = lean_unbox_usize(v_depth_1138_);
lean_dec(v_depth_1138_);
v_res_1145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(v_00_u03b2_1137_, v_depth_boxed_1144_, v_keys_1139_, v_vals_1140_, v_heq_1141_, v_i_1142_, v_entries_1143_);
lean_dec_ref(v_vals_1140_);
lean_dec_ref(v_keys_1139_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(lean_object* v_x_1146_, lean_object* v_keys_1147_, lean_object* v_v_1148_, lean_object* v_k_1149_, lean_object* v_as_1150_, lean_object* v_k_1151_, lean_object* v_x_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_1146_, v_keys_1147_, v_v_1148_, v_k_1149_, v_as_1150_, v_k_1151_, v_x_1152_, v_x_1153_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___boxed(lean_object* v_x_1157_, lean_object* v_keys_1158_, lean_object* v_v_1159_, lean_object* v_k_1160_, lean_object* v_as_1161_, lean_object* v_k_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(v_x_1157_, v_keys_1158_, v_v_1159_, v_k_1160_, v_as_1161_, v_k_1162_, v_x_1163_, v_x_1164_, v_x_1165_, v_x_1166_);
lean_dec_ref(v_k_1162_);
lean_dec_ref(v_keys_1158_);
lean_dec(v_x_1157_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17(lean_object* v_00_u03b2_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(v_x_1169_, v_x_1170_, v_x_1171_, v_x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(lean_object* v_s_1174_, lean_object* v_declName_1175_){
_start:
{
lean_object* v_pre_1176_; lean_object* v_eval_1177_; lean_object* v_post_1178_; lean_object* v_simprocNames_1179_; lean_object* v_erased_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1190_; 
v_pre_1176_ = lean_ctor_get(v_s_1174_, 0);
v_eval_1177_ = lean_ctor_get(v_s_1174_, 1);
v_post_1178_ = lean_ctor_get(v_s_1174_, 2);
v_simprocNames_1179_ = lean_ctor_get(v_s_1174_, 3);
v_erased_1180_ = lean_ctor_get(v_s_1174_, 4);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_s_1174_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1182_ = v_s_1174_;
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_erased_1180_);
lean_inc(v_simprocNames_1179_);
lean_inc(v_post_1178_);
lean_inc(v_eval_1177_);
lean_inc(v_pre_1176_);
lean_dec(v_s_1174_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1184_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_simprocNames_1179_, v_declName_1175_);
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_erased_1180_, v_declName_1175_, v___x_1185_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 4, v___x_1186_);
lean_ctor_set(v___x_1182_, 3, v___x_1184_);
v___x_1188_ = v___x_1182_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_pre_1176_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_eval_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_post_1178_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v___x_1186_);
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
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_unsigned_to_nat(16u);
v___x_1193_ = lean_mk_array(v___x_1192_, v___x_1191_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0);
v___x_1195_ = lean_unsigned_to_nat(0u);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default(void){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs(void){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2);
v___x_1203_ = lean_st_mk_ref(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(lean_object* v_a_1207_, lean_object* v_x_1208_){
_start:
{
if (lean_obj_tag(v_x_1208_) == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
else
{
lean_object* v_key_1210_; lean_object* v_tail_1211_; uint8_t v___x_1212_; 
v_key_1210_ = lean_ctor_get(v_x_1208_, 0);
v_tail_1211_ = lean_ctor_get(v_x_1208_, 2);
v___x_1212_ = lean_name_eq(v_key_1210_, v_a_1207_);
if (v___x_1212_ == 0)
{
v_x_1208_ = v_tail_1211_;
goto _start;
}
else
{
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_a_1214_, lean_object* v_x_1215_){
_start:
{
uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1214_, v_x_1215_);
lean_dec(v_x_1215_);
lean_dec(v_a_1214_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(lean_object* v_m_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_buckets_1220_; lean_object* v___x_1221_; uint64_t v___y_1223_; 
v_buckets_1220_ = lean_ctor_get(v_m_1218_, 1);
v___x_1221_ = lean_array_get_size(v_buckets_1220_);
if (lean_obj_tag(v_a_1219_) == 0)
{
uint64_t v___x_1237_; 
v___x_1237_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1223_ = v___x_1237_;
goto v___jp_1222_;
}
else
{
uint64_t v_hash_1238_; 
v_hash_1238_ = lean_ctor_get_uint64(v_a_1219_, sizeof(void*)*2);
v___y_1223_ = v_hash_1238_;
goto v___jp_1222_;
}
v___jp_1222_:
{
uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v_fold_1226_; uint64_t v___x_1227_; uint64_t v___x_1228_; uint64_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1224_ = 32ULL;
v___x_1225_ = lean_uint64_shift_right(v___y_1223_, v___x_1224_);
v_fold_1226_ = lean_uint64_xor(v___y_1223_, v___x_1225_);
v___x_1227_ = 16ULL;
v___x_1228_ = lean_uint64_shift_right(v_fold_1226_, v___x_1227_);
v___x_1229_ = lean_uint64_xor(v_fold_1226_, v___x_1228_);
v___x_1230_ = lean_uint64_to_usize(v___x_1229_);
v___x_1231_ = lean_usize_of_nat(v___x_1221_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_sub(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_usize_land(v___x_1230_, v___x_1233_);
v___x_1235_ = lean_array_uget_borrowed(v_buckets_1220_, v___x_1234_);
v___x_1236_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1219_, v___x_1235_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(lean_object* v_m_1239_, lean_object* v_a_1240_){
_start:
{
uint8_t v_res_1241_; lean_object* v_r_1242_; 
v_res_1241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1239_, v_a_1240_);
lean_dec(v_a_1240_);
lean_dec_ref(v_m_1239_);
v_r_1242_ = lean_box(v_res_1241_);
return v_r_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(lean_object* v_a_1243_, lean_object* v_b_1244_, lean_object* v_x_1245_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
lean_dec(v_b_1244_);
lean_dec(v_a_1243_);
return v_x_1245_;
}
else
{
lean_object* v_key_1246_; lean_object* v_value_1247_; lean_object* v_tail_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1260_; 
v_key_1246_ = lean_ctor_get(v_x_1245_, 0);
v_value_1247_ = lean_ctor_get(v_x_1245_, 1);
v_tail_1248_ = lean_ctor_get(v_x_1245_, 2);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_x_1245_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1250_ = v_x_1245_;
v_isShared_1251_ = v_isSharedCheck_1260_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_tail_1248_);
lean_inc(v_value_1247_);
lean_inc(v_key_1246_);
lean_dec(v_x_1245_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1260_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_name_eq(v_key_1246_, v_a_1243_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1243_, v_b_1244_, v_tail_1248_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 2, v___x_1253_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_key_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_value_1247_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v___x_1258_; 
lean_dec(v_value_1247_);
lean_dec(v_key_1246_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_b_1244_);
lean_ctor_set(v___x_1250_, 0, v_a_1243_);
v___x_1258_ = v___x_1250_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_b_1244_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_tail_1248_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
return v_x_1261_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1291_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_x_1262_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1267_ = v_x_1262_;
v_isShared_1268_ = v_isSharedCheck_1291_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_tail_1265_);
lean_inc(v_value_1264_);
lean_inc(v_key_1263_);
lean_dec(v_x_1262_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1291_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; uint64_t v___y_1271_; 
v___x_1269_ = lean_array_get_size(v_x_1261_);
if (lean_obj_tag(v_key_1263_) == 0)
{
uint64_t v___x_1289_; 
v___x_1289_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1271_ = v___x_1289_;
goto v___jp_1270_;
}
else
{
uint64_t v_hash_1290_; 
v_hash_1290_ = lean_ctor_get_uint64(v_key_1263_, sizeof(void*)*2);
v___y_1271_ = v_hash_1290_;
goto v___jp_1270_;
}
v___jp_1270_:
{
uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v_fold_1274_; uint64_t v___x_1275_; uint64_t v___x_1276_; uint64_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1272_ = 32ULL;
v___x_1273_ = lean_uint64_shift_right(v___y_1271_, v___x_1272_);
v_fold_1274_ = lean_uint64_xor(v___y_1271_, v___x_1273_);
v___x_1275_ = 16ULL;
v___x_1276_ = lean_uint64_shift_right(v_fold_1274_, v___x_1275_);
v___x_1277_ = lean_uint64_xor(v_fold_1274_, v___x_1276_);
v___x_1278_ = lean_uint64_to_usize(v___x_1277_);
v___x_1279_ = lean_usize_of_nat(v___x_1269_);
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_sub(v___x_1279_, v___x_1280_);
v___x_1282_ = lean_usize_land(v___x_1278_, v___x_1281_);
v___x_1283_ = lean_array_uget_borrowed(v_x_1261_, v___x_1282_);
lean_inc(v___x_1283_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 2, v___x_1283_);
v___x_1285_ = v___x_1267_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_key_1263_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_value_1264_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_array_uset(v_x_1261_, v___x_1282_, v___x_1285_);
v_x_1261_ = v___x_1286_;
v_x_1262_ = v_tail_1265_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(lean_object* v_i_1292_, lean_object* v_source_1293_, lean_object* v_target_1294_){
_start:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = lean_array_get_size(v_source_1293_);
v___x_1296_ = lean_nat_dec_lt(v_i_1292_, v___x_1295_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v_source_1293_);
lean_dec(v_i_1292_);
return v_target_1294_;
}
else
{
lean_object* v_es_1297_; lean_object* v___x_1298_; lean_object* v_source_1299_; lean_object* v_target_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_es_1297_ = lean_array_fget(v_source_1293_, v_i_1292_);
v___x_1298_ = lean_box(0);
v_source_1299_ = lean_array_fset(v_source_1293_, v_i_1292_, v___x_1298_);
v_target_1300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_target_1294_, v_es_1297_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_add(v_i_1292_, v___x_1301_);
lean_dec(v_i_1292_);
v_i_1292_ = v___x_1302_;
v_source_1293_ = v_source_1299_;
v_target_1294_ = v_target_1300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(lean_object* v_data_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_nbuckets_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1305_ = lean_array_get_size(v_data_1304_);
v___x_1306_ = lean_unsigned_to_nat(2u);
v_nbuckets_1307_ = lean_nat_mul(v___x_1305_, v___x_1306_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_mk_array(v_nbuckets_1307_, v___x_1309_);
v___x_1311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v___x_1308_, v_data_1304_, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(lean_object* v_m_1312_, lean_object* v_a_1313_, lean_object* v_b_1314_){
_start:
{
lean_object* v_size_1315_; lean_object* v_buckets_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1362_; 
v_size_1315_ = lean_ctor_get(v_m_1312_, 0);
v_buckets_1316_ = lean_ctor_get(v_m_1312_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_m_1312_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1318_ = v_m_1312_;
v_isShared_1319_ = v_isSharedCheck_1362_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_buckets_1316_);
lean_inc(v_size_1315_);
lean_dec(v_m_1312_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1362_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; uint64_t v___y_1322_; 
v___x_1320_ = lean_array_get_size(v_buckets_1316_);
if (lean_obj_tag(v_a_1313_) == 0)
{
uint64_t v___x_1360_; 
v___x_1360_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1322_ = v___x_1360_;
goto v___jp_1321_;
}
else
{
uint64_t v_hash_1361_; 
v_hash_1361_ = lean_ctor_get_uint64(v_a_1313_, sizeof(void*)*2);
v___y_1322_ = v_hash_1361_;
goto v___jp_1321_;
}
v___jp_1321_:
{
uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v_fold_1325_; uint64_t v___x_1326_; uint64_t v___x_1327_; uint64_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v_bkt_1334_; uint8_t v___x_1335_; 
v___x_1323_ = 32ULL;
v___x_1324_ = lean_uint64_shift_right(v___y_1322_, v___x_1323_);
v_fold_1325_ = lean_uint64_xor(v___y_1322_, v___x_1324_);
v___x_1326_ = 16ULL;
v___x_1327_ = lean_uint64_shift_right(v_fold_1325_, v___x_1326_);
v___x_1328_ = lean_uint64_xor(v_fold_1325_, v___x_1327_);
v___x_1329_ = lean_uint64_to_usize(v___x_1328_);
v___x_1330_ = lean_usize_of_nat(v___x_1320_);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_sub(v___x_1330_, v___x_1331_);
v___x_1333_ = lean_usize_land(v___x_1329_, v___x_1332_);
v_bkt_1334_ = lean_array_uget_borrowed(v_buckets_1316_, v___x_1333_);
v___x_1335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1313_, v_bkt_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v_size_x27_1337_; lean_object* v___x_1338_; lean_object* v_buckets_x27_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1336_ = lean_unsigned_to_nat(1u);
v_size_x27_1337_ = lean_nat_add(v_size_1315_, v___x_1336_);
lean_dec(v_size_1315_);
lean_inc(v_bkt_1334_);
v___x_1338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1338_, 0, v_a_1313_);
lean_ctor_set(v___x_1338_, 1, v_b_1314_);
lean_ctor_set(v___x_1338_, 2, v_bkt_1334_);
v_buckets_x27_1339_ = lean_array_uset(v_buckets_1316_, v___x_1333_, v___x_1338_);
v___x_1340_ = lean_unsigned_to_nat(4u);
v___x_1341_ = lean_nat_mul(v_size_x27_1337_, v___x_1340_);
v___x_1342_ = lean_unsigned_to_nat(3u);
v___x_1343_ = lean_nat_div(v___x_1341_, v___x_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_array_get_size(v_buckets_x27_1339_);
v___x_1345_ = lean_nat_dec_le(v___x_1343_, v___x_1344_);
lean_dec(v___x_1343_);
if (v___x_1345_ == 0)
{
lean_object* v_val_1346_; lean_object* v___x_1348_; 
v_val_1346_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_buckets_x27_1339_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_val_1346_);
lean_ctor_set(v___x_1318_, 0, v_size_x27_1337_);
v___x_1348_ = v___x_1318_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_size_x27_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_val_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
else
{
lean_object* v___x_1351_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_buckets_x27_1339_);
lean_ctor_set(v___x_1318_, 0, v_size_x27_1337_);
v___x_1351_ = v___x_1318_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_size_x27_1337_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_buckets_x27_1339_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v_buckets_x27_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_inc(v_bkt_1334_);
v___x_1353_ = lean_box(0);
v_buckets_x27_1354_ = lean_array_uset(v_buckets_1316_, v___x_1333_, v___x_1353_);
v___x_1355_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1313_, v_b_1314_, v_bkt_1334_);
v___x_1356_ = lean_array_uset(v_buckets_x27_1354_, v___x_1333_, v___x_1355_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v___x_1356_);
v___x_1358_ = v___x_1318_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_size_1315_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0));
v___x_1365_ = lean_mk_io_user_error(v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object* v_declName_1368_, lean_object* v_keys_1369_, lean_object* v_proc_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1412_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1412_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1412_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref(v_proc_1370_);
lean_dec_ref(v_keys_1369_);
lean_dec(v_declName_1368_);
v___x_1378_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 1);
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_keys_1384_; uint8_t v___x_1385_; 
v___x_1382_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_1383_ = lean_st_ref_get(v___x_1382_);
v_keys_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_ref(v_keys_1384_);
lean_dec(v___x_1383_);
v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_keys_1384_, v_declName_1368_);
lean_dec_ref(v_keys_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v_keys_1387_; lean_object* v_procs_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1401_; 
v___x_1386_ = lean_st_ref_take(v___x_1382_);
v_keys_1387_ = lean_ctor_get(v___x_1386_, 0);
v_procs_1388_ = lean_ctor_get(v___x_1386_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1390_ = v___x_1386_;
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_procs_1388_);
lean_inc(v_keys_1387_);
lean_dec(v___x_1386_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_inc(v_declName_1368_);
v___x_1392_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_keys_1387_, v_declName_1368_, v_keys_1369_);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_procs_1388_, v_declName_1368_, v_proc_1370_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v___x_1393_);
lean_ctor_set(v___x_1390_, 0, v___x_1392_);
v___x_1395_ = v___x_1390_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_st_ref_set(v___x_1382_, v___x_1395_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1396_);
v___x_1398_ = v___x_1375_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec_ref(v_proc_1370_);
lean_dec_ref(v_keys_1369_);
v___x_1402_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2));
v___x_1403_ = l_Lean_privateToUserName(v_declName_1368_);
v___x_1404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1403_, v___x_1385_);
v___x_1405_ = lean_string_append(v___x_1402_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
v___x_1408_ = lean_mk_io_user_error(v___x_1407_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 1);
lean_ctor_set(v___x_1375_, 0, v___x_1408_);
v___x_1410_ = v___x_1375_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_proc_1370_);
lean_dec_ref(v_keys_1369_);
lean_dec(v_declName_1368_);
v_a_1413_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1372_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1372_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(lean_object* v_declName_1421_, lean_object* v_keys_1422_, lean_object* v_proc_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v_declName_1421_, v_keys_1422_, v_proc_1423_);
return v_res_1425_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_a_1428_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_1427_, v_a_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_){
_start:
{
uint8_t v_res_1433_; lean_object* v_r_1434_; 
v_res_1433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(v_00_u03b2_1430_, v_m_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_m_1431_);
v_r_1434_ = lean_box(v_res_1433_);
return v_r_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_1436_, v_a_1437_, v_b_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(lean_object* v_00_u03b2_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_1441_, v_x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1444_, lean_object* v_a_1445_, lean_object* v_x_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(v_00_u03b2_1444_, v_a_1445_, v_x_1446_);
lean_dec(v_x_1446_);
lean_dec(v_a_1445_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(lean_object* v_00_u03b2_1449_, lean_object* v_data_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_data_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(lean_object* v_00_u03b2_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_, lean_object* v_x_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_1453_, v_b_1454_, v_x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1457_, lean_object* v_i_1458_, lean_object* v_source_1459_, lean_object* v_target_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v_i_1458_, v_source_1459_, v_target_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1463_, v_x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(lean_object* v_d_u2081_1471_, lean_object* v_d_u2082_1472_){
_start:
{
lean_object* v_declName_1473_; lean_object* v_declName_1474_; uint8_t v___x_1475_; 
v_declName_1473_ = lean_ctor_get(v_d_u2081_1471_, 0);
v_declName_1474_ = lean_ctor_get(v_d_u2082_1472_, 0);
v___x_1475_ = l_Lean_Name_quickLt(v_declName_1473_, v_declName_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(lean_object* v_d_u2081_1476_, lean_object* v_d_u2082_1477_){
_start:
{
uint8_t v_res_1478_; lean_object* v_r_1479_; 
v_res_1478_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_1476_, v_d_u2082_1477_);
lean_dec_ref(v_d_u2082_1477_);
lean_dec_ref(v_d_u2081_1476_);
v_r_1479_ = lean_box(v_res_1478_);
return v_r_1479_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0(void){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
v___x_1484_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1483_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default(void){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState(void){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_s_1488_, lean_object* v_d_1489_){
_start:
{
lean_object* v_builtin_1490_; lean_object* v_newEntries_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1501_; 
v_builtin_1490_ = lean_ctor_get(v_s_1488_, 0);
v_newEntries_1491_ = lean_ctor_get(v_s_1488_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_s_1488_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1493_ = v_s_1488_;
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_newEntries_1491_);
lean_inc(v_builtin_1490_);
lean_dec(v_s_1488_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1501_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_declName_1495_; lean_object* v_keys_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v_declName_1495_ = lean_ctor_get(v_d_1489_, 0);
lean_inc(v_declName_1495_);
v_keys_1496_ = lean_ctor_get(v_d_1489_, 1);
lean_inc_ref(v_keys_1496_);
lean_dec_ref(v_d_1489_);
v___x_1497_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_1491_, v_declName_1495_, v_keys_1496_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1497_);
v___x_1499_ = v___x_1493_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_builtin_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_result_1502_, lean_object* v_declName_1503_, lean_object* v_keys_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_declName_1503_);
lean_ctor_set(v___x_1505_, 1, v_keys_1504_);
v___x_1506_ = lean_array_push(v_result_1502_, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(lean_object* v_as_1508_, lean_object* v_lo_1509_, lean_object* v_hi_1510_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_nat_dec_lt(v_lo_1509_, v_hi_1510_);
if (v___x_1511_ == 0)
{
lean_dec(v_lo_1509_);
return v_as_1508_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_fst_1514_; lean_object* v_snd_1515_; uint8_t v___x_1516_; 
v___x_1512_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___closed__0));
lean_inc(v_lo_1509_);
v___x_1513_ = l_Array_qpartition___redArg(v_as_1508_, v___x_1512_, v_lo_1509_, v_hi_1510_);
v_fst_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_fst_1514_);
v_snd_1515_ = lean_ctor_get(v___x_1513_, 1);
lean_inc(v_snd_1515_);
lean_dec_ref(v___x_1513_);
v___x_1516_ = lean_nat_dec_le(v_hi_1510_, v_fst_1514_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_snd_1515_, v_lo_1509_, v_fst_1514_);
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_nat_add(v_fst_1514_, v___x_1518_);
lean_dec(v_fst_1514_);
v_as_1508_ = v___x_1517_;
v_lo_1509_ = v___x_1519_;
goto _start;
}
else
{
lean_dec(v_fst_1514_);
lean_dec(v_lo_1509_);
return v_snd_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_as_1521_, lean_object* v_lo_1522_, lean_object* v_hi_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_as_1521_, v_lo_1522_, v_hi_1523_);
lean_dec(v_hi_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_1525_, lean_object* v_x1_1526_, lean_object* v_x2_1527_, lean_object* v_x3_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_apply_3(v_f_1525_, v_x1_1526_, v_x2_1527_, v_x3_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_1530_, lean_object* v_keys_1531_, lean_object* v_vals_1532_, lean_object* v_i_1533_, lean_object* v_acc_1534_){
_start:
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = lean_array_get_size(v_keys_1531_);
v___x_1536_ = lean_nat_dec_lt(v_i_1533_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec(v_i_1533_);
lean_dec(v_f_1530_);
return v_acc_1534_;
}
else
{
lean_object* v_k_1537_; lean_object* v_v_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_k_1537_ = lean_array_fget_borrowed(v_keys_1531_, v_i_1533_);
v_v_1538_ = lean_array_fget_borrowed(v_vals_1532_, v_i_1533_);
lean_inc(v_f_1530_);
lean_inc(v_v_1538_);
lean_inc(v_k_1537_);
v___x_1539_ = lean_apply_3(v_f_1530_, v_acc_1534_, v_k_1537_, v_v_1538_);
v___x_1540_ = lean_unsigned_to_nat(1u);
v___x_1541_ = lean_nat_add(v_i_1533_, v___x_1540_);
lean_dec(v_i_1533_);
v_i_1533_ = v___x_1541_;
v_acc_1534_ = v___x_1539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_1543_, lean_object* v_keys_1544_, lean_object* v_vals_1545_, lean_object* v_i_1546_, lean_object* v_acc_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1543_, v_keys_1544_, v_vals_1545_, v_i_1546_, v_acc_1547_);
lean_dec_ref(v_vals_1545_);
lean_dec_ref(v_keys_1544_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v_es_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_es_1552_ = lean_ctor_get(v_x_1550_, 0);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_array_get_size(v_es_1552_);
v___x_1555_ = lean_nat_dec_lt(v___x_1553_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_dec(v_f_1549_);
return v_x_1551_;
}
else
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_nat_dec_le(v___x_1554_, v___x_1554_);
if (v___x_1556_ == 0)
{
if (v___x_1555_ == 0)
{
lean_dec(v_f_1549_);
return v_x_1551_;
}
else
{
size_t v___x_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = ((size_t)0ULL);
v___x_1558_ = lean_usize_of_nat(v___x_1554_);
v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1549_, v_es_1552_, v___x_1557_, v___x_1558_, v_x_1551_);
return v___x_1559_;
}
}
else
{
size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = lean_usize_of_nat(v___x_1554_);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1549_, v_es_1552_, v___x_1560_, v___x_1561_, v_x_1551_);
return v___x_1562_;
}
}
}
else
{
lean_object* v_ks_1563_; lean_object* v_vs_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_ks_1563_ = lean_ctor_get(v_x_1550_, 0);
v_vs_1564_ = lean_ctor_get(v_x_1550_, 1);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1549_, v_ks_1563_, v_vs_1564_, v___x_1565_, v_x_1551_);
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1567_, lean_object* v_as_1568_, size_t v_i_1569_, size_t v_stop_1570_, lean_object* v_b_1571_){
_start:
{
lean_object* v___y_1573_; uint8_t v___x_1577_; 
v___x_1577_ = lean_usize_dec_eq(v_i_1569_, v_stop_1570_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_array_uget_borrowed(v_as_1568_, v_i_1569_);
switch(lean_obj_tag(v___x_1578_))
{
case 0:
{
lean_object* v_key_1579_; lean_object* v_val_1580_; lean_object* v___x_1581_; 
v_key_1579_ = lean_ctor_get(v___x_1578_, 0);
v_val_1580_ = lean_ctor_get(v___x_1578_, 1);
lean_inc(v_f_1567_);
lean_inc(v_val_1580_);
lean_inc(v_key_1579_);
v___x_1581_ = lean_apply_3(v_f_1567_, v_b_1571_, v_key_1579_, v_val_1580_);
v___y_1573_ = v___x_1581_;
goto v___jp_1572_;
}
case 1:
{
lean_object* v_node_1582_; lean_object* v___x_1583_; 
v_node_1582_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_f_1567_);
v___x_1583_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1567_, v_node_1582_, v_b_1571_);
v___y_1573_ = v___x_1583_;
goto v___jp_1572_;
}
default: 
{
v___y_1573_ = v_b_1571_;
goto v___jp_1572_;
}
}
}
else
{
lean_dec(v_f_1567_);
return v_b_1571_;
}
v___jp_1572_:
{
size_t v___x_1574_; size_t v___x_1575_; 
v___x_1574_ = ((size_t)1ULL);
v___x_1575_ = lean_usize_add(v_i_1569_, v___x_1574_);
v_i_1569_ = v___x_1575_;
v_b_1571_ = v___y_1573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1584_, lean_object* v_as_1585_, lean_object* v_i_1586_, lean_object* v_stop_1587_, lean_object* v_b_1588_){
_start:
{
size_t v_i_boxed_1589_; size_t v_stop_boxed_1590_; lean_object* v_res_1591_; 
v_i_boxed_1589_ = lean_unbox_usize(v_i_1586_);
lean_dec(v_i_1586_);
v_stop_boxed_1590_ = lean_unbox_usize(v_stop_1587_);
lean_dec(v_stop_1587_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1584_, v_as_1585_, v_i_boxed_1589_, v_stop_boxed_1590_, v_b_1588_);
lean_dec_ref(v_as_1585_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1592_, v_x_1593_, v_x_1594_);
lean_dec_ref(v_x_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_1596_, lean_object* v_f_1597_, lean_object* v_init_1598_){
_start:
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1599_, 0, v_f_1597_);
v___x_1600_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1599_, v_map_1596_, v_init_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_1601_, lean_object* v_f_1602_, lean_object* v_init_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1601_, v_f_1602_, v_init_1603_);
lean_dec_ref(v_map_1601_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1607_, lean_object* v_s_1608_){
_start:
{
lean_object* v_newEntries_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v_result_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_newEntries_1609_ = lean_ctor_get(v_s_1608_, 1);
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1612_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1609_, v___f_1607_, v___x_1611_);
v___x_1613_ = lean_array_get_size(v_result_1612_);
v___x_1614_ = lean_nat_dec_eq(v___x_1613_, v___x_1610_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___y_1618_; uint8_t v___x_1622_; 
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_sub(v___x_1613_, v___x_1615_);
v___x_1622_ = lean_nat_dec_le(v___x_1610_, v___x_1616_);
if (v___x_1622_ == 0)
{
lean_inc(v___x_1616_);
v___y_1618_ = v___x_1616_;
goto v___jp_1617_;
}
else
{
v___y_1618_ = v___x_1610_;
goto v___jp_1617_;
}
v___jp_1617_:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_nat_dec_le(v___y_1618_, v___x_1616_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec(v___x_1616_);
lean_inc(v___y_1618_);
v___x_1620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_result_1612_, v___y_1618_, v___y_1618_);
lean_dec(v___y_1618_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_result_1612_, v___y_1618_, v___x_1616_);
lean_dec(v___x_1616_);
return v___x_1621_;
}
}
}
else
{
return v_result_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1623_, lean_object* v_s_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1623_, v_s_1624_);
lean_dec_ref(v_s_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_box(0);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_x_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v_x_1628_);
lean_dec_ref(v_x_1628_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___f_1630_, lean_object* v_x_1631_, lean_object* v_s_1632_, uint8_t v_x_1633_){
_start:
{
lean_object* v_newEntries_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_result_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_newEntries_1634_ = lean_ctor_get(v_s_1632_, 1);
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v_result_1637_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1634_, v___f_1630_, v___x_1636_);
v___x_1638_ = lean_array_get_size(v_result_1637_);
v___x_1639_ = lean_nat_dec_eq(v___x_1638_, v___x_1635_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___y_1643_; uint8_t v___x_1647_; 
v___x_1640_ = lean_unsigned_to_nat(1u);
v___x_1641_ = lean_nat_sub(v___x_1638_, v___x_1640_);
v___x_1647_ = lean_nat_dec_le(v___x_1635_, v___x_1641_);
if (v___x_1647_ == 0)
{
lean_inc(v___x_1641_);
v___y_1643_ = v___x_1641_;
goto v___jp_1642_;
}
else
{
v___y_1643_ = v___x_1635_;
goto v___jp_1642_;
}
v___jp_1642_:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_nat_dec_le(v___y_1643_, v___x_1641_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; 
lean_dec(v___x_1641_);
lean_inc(v___y_1643_);
v___x_1645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_result_1637_, v___y_1643_, v___y_1643_);
lean_dec(v___y_1643_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_result_1637_, v___y_1643_, v___x_1641_);
lean_dec(v___x_1641_);
return v___x_1646_;
}
}
}
else
{
return v_result_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___f_1648_, lean_object* v_x_1649_, lean_object* v_s_1650_, lean_object* v_x_1651_){
_start:
{
uint8_t v_x_1576__boxed_1652_; lean_object* v_res_1653_; 
v_x_1576__boxed_1652_ = lean_unbox(v_x_1651_);
v_res_1653_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_1648_, v_x_1649_, v_s_1650_, v_x_1576__boxed_1652_);
lean_dec_ref(v_s_1650_);
lean_dec_ref(v_x_1649_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v_keys_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1666_; 
v___x_1656_ = lean_st_ref_get(v___x_1654_);
v_keys_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v___x_1656_, 1);
lean_dec(v_unused_1667_);
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_keys_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1666_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_keys_1657_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1668_);
lean_dec(v___x_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(lean_object* v___x_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; lean_object* v_keys_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1685_; 
v___x_1675_ = lean_st_ref_get(v___x_1671_);
v_keys_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v___x_1675_, 1);
lean_dec(v_unused_1686_);
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_keys_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_keys_1676_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v___x_1687_, lean_object* v_x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_1687_, v_x_1688_, v___y_1689_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v_x_1688_);
lean_dec(v___x_1687_);
return v_res_1691_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___f_1707_; 
v___x_1706_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1707_, 0, v___x_1706_);
return v___f_1707_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___f_1709_; 
v___x_1708_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_1709_, 0, v___x_1708_);
return v___f_1709_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_box(2);
v___f_1712_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1713_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1714_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___f_1715_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___f_1716_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1717_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1718_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v___f_1716_);
lean_ctor_set(v___x_1718_, 2, v___f_1715_);
lean_ctor_set(v___x_1718_, 3, v___f_1714_);
lean_ctor_set(v___x_1718_, 4, v___f_1713_);
lean_ctor_set(v___x_1718_, 5, v___f_1712_);
lean_ctor_set(v___x_1718_, 6, v___x_1711_);
lean_ctor_set(v___x_1718_, 7, v___x_1710_);
return v___x_1718_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___f_1719_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_));
v___x_1720_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set(v___x_1721_, 1, v___f_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_, &l_Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once, _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
v___x_1724_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_map_1729_, lean_object* v_f_1730_, lean_object* v_init_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_1729_, v_f_1730_, v_init_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_map_1735_, lean_object* v_f_1736_, lean_object* v_init_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(v_00_u03c3_1733_, v_00_u03b2_1734_, v_map_1735_, v_f_1736_, v_init_1737_);
lean_dec_ref(v_map_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(lean_object* v_n_1739_, lean_object* v_as_1740_, lean_object* v_lo_1741_, lean_object* v_hi_1742_, lean_object* v_w_1743_, lean_object* v_hlo_1744_, lean_object* v_hhi_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_as_1740_, v_lo_1741_, v_hi_1742_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(lean_object* v_n_1747_, lean_object* v_as_1748_, lean_object* v_lo_1749_, lean_object* v_hi_1750_, lean_object* v_w_1751_, lean_object* v_hlo_1752_, lean_object* v_hhi_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(v_n_1747_, v_as_1748_, v_lo_1749_, v_hi_1750_, v_w_1751_, v_hlo_1752_, v_hhi_1753_);
lean_dec(v_hi_1750_);
lean_dec(v_n_1747_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_1755_, lean_object* v_f_1756_, lean_object* v_init_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1756_, v_map_1755_, v_init_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_1759_, lean_object* v_f_1760_, lean_object* v_init_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1759_, v_f_1760_, v_init_1761_);
lean_dec_ref(v_map_1759_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_map_1765_, lean_object* v_f_1766_, lean_object* v_init_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1766_, v_map_1765_, v_init_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_1769_, lean_object* v_00_u03b2_1770_, lean_object* v_map_1771_, lean_object* v_f_1772_, lean_object* v_init_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1769_, v_00_u03b2_1770_, v_map_1771_, v_f_1772_, v_init_1773_);
lean_dec_ref(v_map_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1775_, lean_object* v_00_u03b1_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_f_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1778_, v_x_1779_, v_x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1782_, lean_object* v_00_u03b1_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_f_1785_, lean_object* v_x_1786_, lean_object* v_x_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_1782_, v_00_u03b1_1783_, v_00_u03b2_1784_, v_f_1785_, v_x_1786_, v_x_1787_);
lean_dec_ref(v_x_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_00_u03c3_1791_, lean_object* v_f_1792_, lean_object* v_as_1793_, size_t v_i_1794_, size_t v_stop_1795_, lean_object* v_b_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_1792_, v_as_1793_, v_i_1794_, v_stop_1795_, v_b_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_00_u03c3_1800_, lean_object* v_f_1801_, lean_object* v_as_1802_, lean_object* v_i_1803_, lean_object* v_stop_1804_, lean_object* v_b_1805_){
_start:
{
size_t v_i_boxed_1806_; size_t v_stop_boxed_1807_; lean_object* v_res_1808_; 
v_i_boxed_1806_ = lean_unbox_usize(v_i_1803_);
lean_dec(v_i_1803_);
v_stop_boxed_1807_ = lean_unbox_usize(v_stop_1804_);
lean_dec(v_stop_1804_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1798_, v_00_u03b2_1799_, v_00_u03c3_1800_, v_f_1801_, v_as_1802_, v_i_boxed_1806_, v_stop_boxed_1807_, v_b_1805_);
lean_dec_ref(v_as_1802_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_1809_, lean_object* v_00_u03b1_1810_, lean_object* v_00_u03b2_1811_, lean_object* v_f_1812_, lean_object* v_keys_1813_, lean_object* v_vals_1814_, lean_object* v_heq_1815_, lean_object* v_i_1816_, lean_object* v_acc_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1812_, v_keys_1813_, v_vals_1814_, v_i_1816_, v_acc_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_1819_, lean_object* v_00_u03b1_1820_, lean_object* v_00_u03b2_1821_, lean_object* v_f_1822_, lean_object* v_keys_1823_, lean_object* v_vals_1824_, lean_object* v_heq_1825_, lean_object* v_i_1826_, lean_object* v_acc_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03c3_1819_, v_00_u03b1_1820_, v_00_u03b2_1821_, v_f_1822_, v_keys_1823_, v_vals_1824_, v_heq_1825_, v_i_1826_, v_acc_1827_);
lean_dec_ref(v_vals_1824_);
lean_dec_ref(v_keys_1823_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object* v_a_1829_, lean_object* v_x_1830_){
_start:
{
if (lean_obj_tag(v_x_1830_) == 0)
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_box(0);
return v___x_1831_;
}
else
{
lean_object* v_key_1832_; lean_object* v_value_1833_; lean_object* v_tail_1834_; uint8_t v___x_1835_; 
v_key_1832_ = lean_ctor_get(v_x_1830_, 0);
v_value_1833_ = lean_ctor_get(v_x_1830_, 1);
v_tail_1834_ = lean_ctor_get(v_x_1830_, 2);
v___x_1835_ = lean_name_eq(v_key_1832_, v_a_1829_);
if (v___x_1835_ == 0)
{
v_x_1830_ = v_tail_1834_;
goto _start;
}
else
{
lean_object* v___x_1837_; 
lean_inc(v_value_1833_);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v_value_1833_);
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1838_, v_x_1839_);
lean_dec(v_x_1839_);
lean_dec(v_a_1838_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(lean_object* v_m_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_buckets_1843_; lean_object* v___x_1844_; uint64_t v___y_1846_; 
v_buckets_1843_ = lean_ctor_get(v_m_1841_, 1);
v___x_1844_ = lean_array_get_size(v_buckets_1843_);
if (lean_obj_tag(v_a_1842_) == 0)
{
uint64_t v___x_1860_; 
v___x_1860_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1846_ = v___x_1860_;
goto v___jp_1845_;
}
else
{
uint64_t v_hash_1861_; 
v_hash_1861_ = lean_ctor_get_uint64(v_a_1842_, sizeof(void*)*2);
v___y_1846_ = v_hash_1861_;
goto v___jp_1845_;
}
v___jp_1845_:
{
uint64_t v___x_1847_; uint64_t v___x_1848_; uint64_t v_fold_1849_; uint64_t v___x_1850_; uint64_t v___x_1851_; uint64_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1847_ = 32ULL;
v___x_1848_ = lean_uint64_shift_right(v___y_1846_, v___x_1847_);
v_fold_1849_ = lean_uint64_xor(v___y_1846_, v___x_1848_);
v___x_1850_ = 16ULL;
v___x_1851_ = lean_uint64_shift_right(v_fold_1849_, v___x_1850_);
v___x_1852_ = lean_uint64_xor(v_fold_1849_, v___x_1851_);
v___x_1853_ = lean_uint64_to_usize(v___x_1852_);
v___x_1854_ = lean_usize_of_nat(v___x_1844_);
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_sub(v___x_1854_, v___x_1855_);
v___x_1857_ = lean_usize_land(v___x_1853_, v___x_1856_);
v___x_1858_ = lean_array_uget_borrowed(v_buckets_1843_, v___x_1857_);
v___x_1859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_1842_, v___x_1858_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* v_m_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_m_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(lean_object* v_as_1865_, lean_object* v_k_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v_m_1871_; lean_object* v_a_1872_; uint8_t v___x_1873_; 
v___x_1869_ = lean_nat_add(v_x_1867_, v_x_1868_);
v___x_1870_ = lean_unsigned_to_nat(1u);
v_m_1871_ = lean_nat_shiftr(v___x_1869_, v___x_1870_);
lean_dec(v___x_1869_);
v_a_1872_ = lean_array_fget_borrowed(v_as_1865_, v_m_1871_);
v___x_1873_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_a_1872_, v_k_1866_);
if (v___x_1873_ == 0)
{
uint8_t v___x_1874_; 
lean_dec(v_x_1868_);
v___x_1874_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_k_1866_, v_a_1872_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
lean_dec(v_m_1871_);
lean_dec(v_x_1867_);
lean_inc(v_a_1872_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1872_);
return v___x_1875_;
}
else
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_nat_dec_eq(v_m_1871_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = lean_nat_sub(v_m_1871_, v___x_1870_);
lean_dec(v_m_1871_);
v___x_1879_ = lean_nat_dec_lt(v___x_1878_, v_x_1867_);
if (v___x_1879_ == 0)
{
v_x_1868_ = v___x_1878_;
goto _start;
}
else
{
lean_object* v___x_1881_; 
lean_dec(v___x_1878_);
lean_dec(v_x_1867_);
v___x_1881_ = lean_box(0);
return v___x_1881_;
}
}
else
{
lean_object* v___x_1882_; 
lean_dec(v_m_1871_);
lean_dec(v_x_1867_);
v___x_1882_ = lean_box(0);
return v___x_1882_;
}
}
}
else
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
lean_dec(v_x_1867_);
v___x_1883_ = lean_nat_add(v_m_1871_, v___x_1870_);
lean_dec(v_m_1871_);
v___x_1884_ = lean_nat_dec_le(v___x_1883_, v_x_1868_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; 
lean_dec(v___x_1883_);
lean_dec(v_x_1868_);
v___x_1885_ = lean_box(0);
return v___x_1885_;
}
else
{
v_x_1867_ = v___x_1883_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object* v_as_1887_, lean_object* v_k_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_1887_, v_k_1888_, v_x_1889_, v_x_1890_);
lean_dec_ref(v_k_1888_);
lean_dec_ref(v_as_1887_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_1892_, lean_object* v_vals_1893_, lean_object* v_i_1894_, lean_object* v_k_1895_){
_start:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_array_get_size(v_keys_1892_);
v___x_1897_ = lean_nat_dec_lt(v_i_1894_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec(v_i_1894_);
v___x_1898_ = lean_box(0);
return v___x_1898_;
}
else
{
lean_object* v_k_x27_1899_; uint8_t v___x_1900_; 
v_k_x27_1899_ = lean_array_fget_borrowed(v_keys_1892_, v_i_1894_);
v___x_1900_ = lean_name_eq(v_k_1895_, v_k_x27_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_nat_add(v_i_1894_, v___x_1901_);
lean_dec(v_i_1894_);
v_i_1894_ = v___x_1902_;
goto _start;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_array_fget_borrowed(v_vals_1893_, v_i_1894_);
lean_dec(v_i_1894_);
lean_inc(v___x_1904_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_1906_, lean_object* v_vals_1907_, lean_object* v_i_1908_, lean_object* v_k_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_1906_, v_vals_1907_, v_i_1908_, v_k_1909_);
lean_dec(v_k_1909_);
lean_dec_ref(v_vals_1907_);
lean_dec_ref(v_keys_1906_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object* v_x_1911_, size_t v_x_1912_, lean_object* v_x_1913_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_object* v_es_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1935_; 
v_es_1914_ = lean_ctor_get(v_x_1911_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_x_1911_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1916_ = v_x_1911_;
v_isShared_1917_ = v_isSharedCheck_1935_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_es_1914_);
lean_dec(v_x_1911_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1935_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; size_t v___x_1919_; size_t v___x_1920_; size_t v___x_1921_; lean_object* v_j_1922_; lean_object* v___x_1923_; 
v___x_1918_ = lean_box(2);
v___x_1919_ = ((size_t)5ULL);
v___x_1920_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_1921_ = lean_usize_land(v_x_1912_, v___x_1920_);
v_j_1922_ = lean_usize_to_nat(v___x_1921_);
v___x_1923_ = lean_array_get(v___x_1918_, v_es_1914_, v_j_1922_);
lean_dec(v_j_1922_);
lean_dec_ref(v_es_1914_);
switch(lean_obj_tag(v___x_1923_))
{
case 0:
{
lean_object* v_key_1924_; lean_object* v_val_1925_; uint8_t v___x_1926_; 
v_key_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_key_1924_);
v_val_1925_ = lean_ctor_get(v___x_1923_, 1);
lean_inc(v_val_1925_);
lean_dec_ref(v___x_1923_);
v___x_1926_ = lean_name_eq(v_x_1913_, v_key_1924_);
lean_dec(v_key_1924_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec(v_val_1925_);
lean_del_object(v___x_1916_);
v___x_1927_ = lean_box(0);
return v___x_1927_;
}
else
{
lean_object* v___x_1929_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
lean_ctor_set(v___x_1916_, 0, v_val_1925_);
v___x_1929_ = v___x_1916_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_val_1925_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
case 1:
{
lean_object* v_node_1931_; size_t v___x_1932_; 
lean_del_object(v___x_1916_);
v_node_1931_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_node_1931_);
lean_dec_ref(v___x_1923_);
v___x_1932_ = lean_usize_shift_right(v_x_1912_, v___x_1919_);
v_x_1911_ = v_node_1931_;
v_x_1912_ = v___x_1932_;
goto _start;
}
default: 
{
lean_object* v___x_1934_; 
lean_del_object(v___x_1916_);
v___x_1934_ = lean_box(0);
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_ks_1936_; lean_object* v_vs_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_ks_1936_ = lean_ctor_get(v_x_1911_, 0);
lean_inc_ref(v_ks_1936_);
v_vs_1937_ = lean_ctor_get(v_x_1911_, 1);
lean_inc_ref(v_vs_1937_);
lean_dec_ref(v_x_1911_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_ks_1936_, v_vs_1937_, v___x_1938_, v_x_1913_);
lean_dec_ref(v_vs_1937_);
lean_dec_ref(v_ks_1936_);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
size_t v_x_2007__boxed_1943_; lean_object* v_res_1944_; 
v_x_2007__boxed_1943_ = lean_unbox_usize(v_x_1941_);
lean_dec(v_x_1941_);
v_res_1944_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_1940_, v_x_2007__boxed_1943_, v_x_1942_);
lean_dec(v_x_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(lean_object* v_x_1945_, lean_object* v_x_1946_){
_start:
{
uint64_t v___y_1948_; 
if (lean_obj_tag(v_x_1946_) == 0)
{
uint64_t v___x_1951_; 
v___x_1951_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1948_ = v___x_1951_;
goto v___jp_1947_;
}
else
{
uint64_t v_hash_1952_; 
v_hash_1952_ = lean_ctor_get_uint64(v_x_1946_, sizeof(void*)*2);
v___y_1948_ = v_hash_1952_;
goto v___jp_1947_;
}
v___jp_1947_:
{
size_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_uint64_to_usize(v___y_1948_);
v___x_1950_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_1945_, v___x_1949_, v_x_1946_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object* v_x_1953_, lean_object* v_x_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_1953_, v_x_1954_);
lean_dec(v_x_1954_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(lean_object* v_declName_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v___x_1961_; lean_object* v_env_1962_; lean_object* v___x_1963_; lean_object* v___x_1973_; 
v___x_1961_ = lean_st_ref_get(v_a_1959_);
v_env_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc_ref(v_env_1962_);
lean_dec(v___x_1961_);
v___x_1963_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_1973_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1962_, v_declName_1958_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; lean_object* v_toEnvExtension_1975_; lean_object* v_asyncMode_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v_newEntries_1979_; lean_object* v___x_1980_; 
v___x_1974_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc_ref(v_toEnvExtension_1975_);
v_asyncMode_1976_ = lean_ctor_get(v_toEnvExtension_1975_, 2);
lean_inc(v_asyncMode_1976_);
lean_dec_ref(v_toEnvExtension_1975_);
v___x_1977_ = lean_box(0);
lean_inc_ref(v_env_1962_);
v___x_1978_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1963_, v___x_1974_, v_env_1962_, v_asyncMode_1976_, v___x_1977_);
lean_dec(v_asyncMode_1976_);
v_newEntries_1979_ = lean_ctor_get(v___x_1978_, 1);
lean_inc_ref(v_newEntries_1979_);
lean_dec(v___x_1978_);
v___x_1980_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_1979_, v_declName_1958_);
if (lean_obj_tag(v___x_1980_) == 1)
{
lean_object* v___x_1981_; 
lean_dec_ref(v_env_1962_);
lean_dec(v_declName_1958_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
else
{
lean_dec(v___x_1980_);
goto v___jp_1964_;
}
}
else
{
lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2010_; 
v_val_1982_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1984_ = v___x_1973_;
v_isShared_1985_ = v_isSharedCheck_2010_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_dec(v___x_1973_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2010_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1986_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v___x_1987_ = 0;
v___x_1988_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1963_, v___x_1986_, v_env_1962_, v_val_1982_, v___x_1987_);
lean_dec(v_val_1982_);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_array_get_size(v___x_1988_);
v___x_1991_ = lean_nat_dec_lt(v___x_1989_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_dec_ref(v___x_1988_);
lean_del_object(v___x_1984_);
goto v___jp_1964_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_sub(v___x_1990_, v___x_1992_);
v___x_1994_ = lean_nat_dec_le(v___x_1989_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec(v___x_1993_);
lean_dec_ref(v___x_1988_);
lean_del_object(v___x_1984_);
goto v___jp_1964_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___closed__0));
lean_inc(v_declName_1958_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_declName_1958_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v___x_1988_, v___x_1996_, v___x_1989_, v___x_1993_);
lean_dec_ref(v___x_1996_);
lean_dec_ref(v___x_1988_);
if (lean_obj_tag(v___x_1997_) == 1)
{
lean_object* v_val_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_env_1962_);
lean_dec(v_declName_1958_);
v_val_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_val_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2009_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_keys_2002_; lean_object* v___x_2004_; 
v_keys_2002_ = lean_ctor_get(v_val_1998_, 1);
lean_inc_ref(v_keys_2002_);
lean_dec(v_val_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v_keys_2002_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_keys_2002_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 0);
lean_ctor_set(v___x_1984_, 0, v___x_2004_);
v___x_2006_ = v___x_1984_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
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
lean_dec(v___x_1997_);
lean_del_object(v___x_1984_);
goto v___jp_1964_;
}
}
}
}
}
v___jp_1964_:
{
lean_object* v___x_1965_; lean_object* v_toEnvExtension_1966_; lean_object* v_asyncMode_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_builtin_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1965_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc_ref(v_toEnvExtension_1966_);
v_asyncMode_1967_ = lean_ctor_get(v_toEnvExtension_1966_, 2);
lean_inc(v_asyncMode_1967_);
lean_dec_ref(v_toEnvExtension_1966_);
v___x_1968_ = lean_box(0);
v___x_1969_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1963_, v___x_1965_, v_env_1962_, v_asyncMode_1967_, v___x_1968_);
lean_dec(v_asyncMode_1967_);
v_builtin_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc_ref(v_builtin_1970_);
lean_dec(v___x_1969_);
v___x_1971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_1970_, v_declName_1958_);
lean_dec(v_declName_1958_);
lean_dec_ref(v_builtin_1970_);
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(lean_object* v_declName_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2011_, v_a_2012_);
lean_dec(v_a_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(lean_object* v_declName_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2015_, v_a_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(lean_object* v_declName_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(lean_object* v_00_u03b2_2025_, lean_object* v_m_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_2026_, v_a_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(lean_object* v_00_u03b2_2029_, lean_object* v_m_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(v_00_u03b2_2029_, v_m_2030_, v_a_2031_);
lean_dec(v_a_2031_);
lean_dec_ref(v_m_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(lean_object* v_00_u03b2_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_2034_, v_x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(lean_object* v_00_u03b2_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(v_00_u03b2_2037_, v_x_2038_, v_x_2039_);
lean_dec(v_x_2039_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(lean_object* v_as_2041_, lean_object* v_k_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_2041_, v_k_2042_, v_x_2043_, v_x_2044_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(lean_object* v_as_2047_, lean_object* v_k_2048_, lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(v_as_2047_, v_k_2048_, v_x_2049_, v_x_2050_, v_x_2051_);
lean_dec_ref(v_k_2048_);
lean_dec_ref(v_as_2047_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2053_, lean_object* v_a_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_2054_, v_x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2057_, lean_object* v_a_2058_, lean_object* v_x_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(v_00_u03b2_2057_, v_a_2058_, v_x_2059_);
lean_dec(v_x_2059_);
lean_dec(v_a_2058_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2061_, lean_object* v_x_2062_, size_t v_x_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_2062_, v_x_2063_, v_x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
size_t v_x_2221__boxed_2070_; lean_object* v_res_2071_; 
v_x_2221__boxed_2070_ = lean_unbox_usize(v_x_2068_);
lean_dec(v_x_2068_);
v_res_2071_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_2066_, v_x_2067_, v_x_2221__boxed_2070_, v_x_2069_);
lean_dec(v_x_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2072_, lean_object* v_keys_2073_, lean_object* v_vals_2074_, lean_object* v_heq_2075_, lean_object* v_i_2076_, lean_object* v_k_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_2073_, v_vals_2074_, v_i_2076_, v_k_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2079_, lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_heq_2082_, lean_object* v_i_2083_, lean_object* v_k_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(v_00_u03b2_2079_, v_keys_2080_, v_vals_2081_, v_heq_2082_, v_i_2083_, v_k_2084_);
lean_dec(v_k_2084_);
lean_dec_ref(v_vals_2081_);
lean_dec_ref(v_keys_2080_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(lean_object* v_declName_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2104_; 
v___x_2089_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2086_, v_a_2087_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2104_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
if (lean_obj_tag(v_a_2090_) == 0)
{
uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2094_ = 0;
v___x_2095_ = lean_box(v___x_2094_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2095_);
v___x_2097_ = v___x_2092_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
else
{
uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec_ref(v_a_2090_);
v___x_2099_ = 1;
v___x_2100_ = lean_box(v___x_2099_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2100_);
v___x_2102_ = v___x_2092_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(lean_object* v_declName_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2105_, v_a_2106_);
lean_dec(v_a_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc(lean_object* v_declName_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2109_, v_a_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(lean_object* v_declName_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(lean_object* v_declName_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2122_; lean_object* v_env_2123_; lean_object* v___x_2124_; lean_object* v_toEnvExtension_2125_; lean_object* v_asyncMode_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v_builtin_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2122_ = lean_st_ref_get(v_a_2120_);
v_env_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc_ref(v_env_2123_);
lean_dec(v___x_2122_);
v___x_2124_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc_ref(v_toEnvExtension_2125_);
v_asyncMode_2126_ = lean_ctor_get(v_toEnvExtension_2125_, 2);
lean_inc(v_asyncMode_2126_);
lean_dec_ref(v_toEnvExtension_2125_);
v___x_2127_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
v___x_2128_ = lean_box(0);
v___x_2129_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2127_, v___x_2124_, v_env_2123_, v_asyncMode_2126_, v___x_2128_);
lean_dec(v_asyncMode_2126_);
v_builtin_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc_ref(v_builtin_2130_);
lean_dec(v___x_2129_);
v___x_2131_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_builtin_2130_, v_declName_2119_);
lean_dec_ref(v_builtin_2130_);
v___x_2132_ = lean_box(v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(lean_object* v_declName_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2134_, v_a_2135_);
lean_dec(v_a_2135_);
lean_dec(v_declName_2134_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(lean_object* v_declName_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_2138_, v_a_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(lean_object* v_declName_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_declName_2143_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(lean_object* v_declName_2148_, lean_object* v_keys_2149_, lean_object* v_s_2150_){
_start:
{
lean_object* v_builtin_2151_; lean_object* v_newEntries_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2160_; 
v_builtin_2151_ = lean_ctor_get(v_s_2150_, 0);
v_newEntries_2152_ = lean_ctor_get(v_s_2150_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_s_2150_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2154_ = v_s_2150_;
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_newEntries_2152_);
lean_inc(v_builtin_2151_);
lean_dec(v_s_2150_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_2152_, v_declName_2148_, v_keys_2149_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_builtin_2151_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
lean_ctor_set(v___x_2166_, 2, v___x_2165_);
lean_ctor_set(v___x_2166_, 3, v___x_2164_);
lean_ctor_set(v___x_2166_, 4, v___x_2164_);
lean_ctor_set(v___x_2166_, 5, v___x_2164_);
lean_ctor_set(v___x_2166_, 6, v___x_2164_);
lean_ctor_set(v___x_2166_, 7, v___x_2164_);
lean_ctor_set(v___x_2166_, 8, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_unsigned_to_nat(32u);
v___x_2168_ = lean_mk_empty_array_with_capacity(v___x_2167_);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2170_ = ((size_t)5ULL);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_unsigned_to_nat(32u);
v___x_2173_ = lean_mk_empty_array_with_capacity(v___x_2172_);
v___x_2174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3);
v___x_2175_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v___x_2173_);
lean_ctor_set(v___x_2175_, 2, v___x_2171_);
lean_ctor_set(v___x_2175_, 3, v___x_2171_);
lean_ctor_set_usize(v___x_2175_, 4, v___x_2170_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2176_ = lean_box(1);
v___x_2177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4);
v___x_2178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
lean_ctor_set(v___x_2179_, 2, v___x_2176_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(lean_object* v_msgData_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; lean_object* v_env_2185_; lean_object* v_options_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2184_ = lean_st_ref_get(v___y_2182_);
v_env_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc_ref(v_env_2185_);
lean_dec(v___x_2184_);
v_options_2186_ = lean_ctor_get(v___y_2181_, 2);
v___x_2187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2188_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2186_);
v___x_2189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2189_, 0, v_env_2185_);
lean_ctor_set(v___x_2189_, 1, v___x_2187_);
lean_ctor_set(v___x_2189_, 2, v___x_2188_);
lean_ctor_set(v___x_2189_, 3, v_options_2186_);
v___x_2190_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v_msgData_2180_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(lean_object* v_msgData_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(lean_object* v_msg_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_ref_2201_; lean_object* v___x_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2211_; 
v_ref_2201_ = lean_ctor_get(v___y_2198_, 5);
v___x_2202_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msg_2197_, v___y_2198_, v___y_2199_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
lean_inc(v_ref_2201_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_ref_2201_);
lean_ctor_set(v___x_2207_, 1, v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set_tag(v___x_2205_, 1);
lean_ctor_set(v___x_2205_, 0, v___x_2207_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(lean_object* v_msg_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2216_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0(void){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1);
v___x_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(lean_object* v_declName_2230_, lean_object* v_keys_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v___x_2235_; lean_object* v_env_2236_; lean_object* v___f_2237_; lean_object* v___y_2239_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___x_2287_; 
v___x_2235_ = lean_st_ref_get(v_a_2233_);
v_env_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_ref(v_env_2236_);
lean_dec(v___x_2235_);
lean_inc(v_declName_2230_);
v___f_2237_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0), 3, 2);
lean_closure_set(v___f_2237_, 0, v_declName_2230_);
lean_closure_set(v___f_2237_, 1, v_keys_2231_);
v___x_2287_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2236_, v_declName_2230_);
lean_dec_ref(v_env_2236_);
if (lean_obj_tag(v___x_2287_) == 0)
{
v___y_2267_ = v_a_2232_;
v___y_2268_ = v_a_2233_;
goto v___jp_2266_;
}
else
{
uint8_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec_ref(v___x_2287_);
lean_dec_ref(v___f_2237_);
v___x_2288_ = 0;
v___x_2289_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2290_ = l_Lean_MessageData_ofConstName(v_declName_2230_, v___x_2288_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2293_, v_a_2232_, v_a_2233_);
return v___x_2294_;
}
v___jp_2238_:
{
lean_object* v___x_2240_; lean_object* v_env_2241_; lean_object* v_nextMacroScope_2242_; lean_object* v_ngen_2243_; lean_object* v_auxDeclNGen_2244_; lean_object* v_traceState_2245_; lean_object* v_messages_2246_; lean_object* v_infoState_2247_; lean_object* v_snapshotTasks_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2264_; 
v___x_2240_ = lean_st_ref_take(v___y_2239_);
v_env_2241_ = lean_ctor_get(v___x_2240_, 0);
v_nextMacroScope_2242_ = lean_ctor_get(v___x_2240_, 1);
v_ngen_2243_ = lean_ctor_get(v___x_2240_, 2);
v_auxDeclNGen_2244_ = lean_ctor_get(v___x_2240_, 3);
v_traceState_2245_ = lean_ctor_get(v___x_2240_, 4);
v_messages_2246_ = lean_ctor_get(v___x_2240_, 6);
v_infoState_2247_ = lean_ctor_get(v___x_2240_, 7);
v_snapshotTasks_2248_ = lean_ctor_get(v___x_2240_, 8);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v___x_2240_, 5);
lean_dec(v_unused_2265_);
v___x_2250_ = v___x_2240_;
v_isShared_2251_ = v_isSharedCheck_2264_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_snapshotTasks_2248_);
lean_inc(v_infoState_2247_);
lean_inc(v_messages_2246_);
lean_inc(v_traceState_2245_);
lean_inc(v_auxDeclNGen_2244_);
lean_inc(v_ngen_2243_);
lean_inc(v_nextMacroScope_2242_);
lean_inc(v_env_2241_);
lean_dec(v___x_2240_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2264_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; lean_object* v_toEnvExtension_2253_; lean_object* v_asyncMode_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2252_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
v_toEnvExtension_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc_ref(v_toEnvExtension_2253_);
v_asyncMode_2254_ = lean_ctor_get(v_toEnvExtension_2253_, 2);
lean_inc(v_asyncMode_2254_);
lean_dec_ref(v_toEnvExtension_2253_);
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_2252_, v_env_2241_, v___f_2237_, v_asyncMode_2254_, v___x_2255_);
lean_dec(v_asyncMode_2254_);
v___x_2257_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 5, v___x_2257_);
lean_ctor_set(v___x_2250_, 0, v___x_2256_);
v___x_2259_ = v___x_2250_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_nextMacroScope_2242_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_ngen_2243_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_auxDeclNGen_2244_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_traceState_2245_);
lean_ctor_set(v_reuseFailAlloc_2263_, 5, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2263_, 6, v_messages_2246_);
lean_ctor_set(v_reuseFailAlloc_2263_, 7, v_infoState_2247_);
lean_ctor_set(v_reuseFailAlloc_2263_, 8, v_snapshotTasks_2248_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_st_ref_set(v___y_2239_, v___x_2259_);
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
}
v___jp_2266_:
{
lean_object* v___x_2269_; 
lean_inc(v_declName_2230_);
v___x_2269_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_2230_, v___y_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; uint8_t v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = lean_unbox(v_a_2270_);
lean_dec(v_a_2270_);
if (v___x_2271_ == 0)
{
lean_dec(v_declName_2230_);
v___y_2239_ = v___y_2268_;
goto v___jp_2238_;
}
else
{
lean_object* v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec_ref(v___f_2237_);
v___x_2272_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4);
v___x_2273_ = 0;
v___x_2274_ = l_Lean_MessageData_ofConstName(v_declName_2230_, v___x_2273_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2272_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2277_, v___y_2267_, v___y_2268_);
return v___x_2278_;
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v___f_2237_);
lean_dec(v_declName_2230_);
v_a_2279_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2269_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2269_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(lean_object* v_declName_2295_, lean_object* v_keys_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(v_declName_2295_, v_keys_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(lean_object* v_00_u03b1_2301_, lean_object* v_msg_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v_msg_2302_, v___y_2303_, v___y_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_msg_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(v_00_u03b1_2307_, v_msg_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(lean_object* v_e_2313_){
_start:
{
if (lean_obj_tag(v_e_2313_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2323_; 
v_a_2315_ = lean_ctor_get(v_e_2313_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_e_2313_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2317_ = v_e_2313_;
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v_e_2313_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = lean_mk_io_user_error(v_a_2315_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 1);
lean_ctor_set(v___x_2317_, 0, v___x_2319_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
v_a_2324_ = lean_ctor_get(v_e_2313_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_e_2313_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v_e_2313_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v_e_2313_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 0);
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(lean_object* v_00_u03b1_2335_, lean_object* v_e_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v_e_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_2339_, lean_object* v_e_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(v_00_u03b1_2339_, v_e_2340_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(lean_object* v_declName_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_env_2353_; lean_object* v_opts_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; 
v_env_2353_ = lean_ctor_get(v_a_2351_, 0);
lean_inc_ref(v_env_2353_);
v_opts_2354_ = lean_ctor_get(v_a_2351_, 1);
lean_inc_ref(v_opts_2354_);
lean_dec_ref(v_a_2351_);
v___x_2355_ = 0;
lean_inc(v_declName_2350_);
lean_inc_ref(v_env_2353_);
v___x_2356_ = l_Lean_Environment_find_x3f(v_env_2353_, v_declName_2350_, v___x_2355_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
v___x_2357_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0));
v___x_2358_ = 1;
v___x_2359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2350_, v___x_2358_);
v___x_2360_ = lean_string_append(v___x_2357_, v___x_2359_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2362_ = lean_string_append(v___x_2360_, v___x_2361_);
v___x_2363_ = lean_mk_io_user_error(v___x_2362_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v_val_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2410_; 
v_val_2365_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2367_ = v___x_2356_;
v_isShared_2368_ = v_isSharedCheck_2410_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_val_2365_);
lean_dec(v___x_2356_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2410_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_ConstantInfo_type(v_val_2365_);
if (lean_obj_tag(v___x_2386_) == 4)
{
lean_object* v_declName_2387_; 
v_declName_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_declName_2387_);
lean_dec_ref(v___x_2386_);
if (lean_obj_tag(v_declName_2387_) == 1)
{
lean_object* v_pre_2388_; 
v_pre_2388_ = lean_ctor_get(v_declName_2387_, 0);
lean_inc(v_pre_2388_);
if (lean_obj_tag(v_pre_2388_) == 1)
{
lean_object* v_pre_2389_; 
v_pre_2389_ = lean_ctor_get(v_pre_2388_, 0);
lean_inc(v_pre_2389_);
if (lean_obj_tag(v_pre_2389_) == 1)
{
lean_object* v_pre_2390_; 
v_pre_2390_ = lean_ctor_get(v_pre_2389_, 0);
lean_inc(v_pre_2390_);
if (lean_obj_tag(v_pre_2390_) == 1)
{
lean_object* v_pre_2391_; 
v_pre_2391_ = lean_ctor_get(v_pre_2390_, 0);
lean_inc(v_pre_2391_);
if (lean_obj_tag(v_pre_2391_) == 1)
{
lean_object* v_pre_2392_; 
v_pre_2392_ = lean_ctor_get(v_pre_2391_, 0);
if (lean_obj_tag(v_pre_2392_) == 0)
{
lean_object* v_str_2393_; lean_object* v_str_2394_; lean_object* v_str_2395_; lean_object* v_str_2396_; lean_object* v_str_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_str_2393_ = lean_ctor_get(v_declName_2387_, 1);
lean_inc_ref(v_str_2393_);
lean_dec_ref(v_declName_2387_);
v_str_2394_ = lean_ctor_get(v_pre_2388_, 1);
lean_inc_ref(v_str_2394_);
lean_dec_ref(v_pre_2388_);
v_str_2395_ = lean_ctor_get(v_pre_2389_, 1);
lean_inc_ref(v_str_2395_);
lean_dec_ref(v_pre_2389_);
v_str_2396_ = lean_ctor_get(v_pre_2390_, 1);
lean_inc_ref(v_str_2396_);
lean_dec_ref(v_pre_2390_);
v_str_2397_ = lean_ctor_get(v_pre_2391_, 1);
lean_inc_ref(v_str_2397_);
lean_dec_ref(v_pre_2391_);
v___x_2398_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0));
v___x_2399_ = lean_string_dec_eq(v_str_2397_, v___x_2398_);
lean_dec_ref(v_str_2397_);
if (v___x_2399_ == 0)
{
lean_dec_ref(v_str_2396_);
lean_dec_ref(v_str_2395_);
lean_dec_ref(v_str_2394_);
lean_dec_ref(v_str_2393_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
else
{
lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1));
v___x_2401_ = lean_string_dec_eq(v_str_2396_, v___x_2400_);
lean_dec_ref(v_str_2396_);
if (v___x_2401_ == 0)
{
lean_dec_ref(v_str_2395_);
lean_dec_ref(v_str_2394_);
lean_dec_ref(v_str_2393_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
else
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4));
v___x_2403_ = lean_string_dec_eq(v_str_2395_, v___x_2402_);
lean_dec_ref(v_str_2395_);
if (v___x_2403_ == 0)
{
lean_dec_ref(v_str_2394_);
lean_dec_ref(v_str_2393_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
else
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5));
v___x_2405_ = lean_string_dec_eq(v_str_2394_, v___x_2404_);
lean_dec_ref(v_str_2394_);
if (v___x_2405_ == 0)
{
lean_dec_ref(v_str_2393_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
else
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6));
v___x_2407_ = lean_string_dec_eq(v_str_2393_, v___x_2406_);
lean_dec_ref(v_str_2393_);
if (v___x_2407_ == 0)
{
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_del_object(v___x_2367_);
lean_dec(v_val_2365_);
v___x_2408_ = l_Lean_Environment_evalConst___redArg(v_env_2353_, v_opts_2354_, v_declName_2350_, v___x_2407_);
lean_dec_ref(v_opts_2354_);
v___x_2409_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v___x_2408_);
return v___x_2409_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2391_);
lean_dec_ref(v_pre_2390_);
lean_dec_ref(v_pre_2389_);
lean_dec_ref(v_pre_2388_);
lean_dec_ref(v_declName_2387_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
}
else
{
lean_dec(v_pre_2391_);
lean_dec_ref(v_pre_2390_);
lean_dec_ref(v_pre_2389_);
lean_dec_ref(v_pre_2388_);
lean_dec_ref(v_declName_2387_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
}
else
{
lean_dec(v_pre_2390_);
lean_dec_ref(v_pre_2389_);
lean_dec_ref(v_pre_2388_);
lean_dec_ref(v_declName_2387_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
}
else
{
lean_dec_ref(v_pre_2388_);
lean_dec(v_pre_2389_);
lean_dec_ref(v_declName_2387_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
}
else
{
lean_dec(v_pre_2388_);
lean_dec_ref(v_declName_2387_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
}
else
{
lean_dec(v_declName_2387_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
}
else
{
lean_dec_ref(v___x_2386_);
lean_dec_ref(v_opts_2354_);
lean_dec_ref(v_env_2353_);
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2370_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2));
v___x_2371_ = l_Lean_privateToUserName(v_declName_2350_);
v___x_2372_ = 1;
v___x_2373_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2371_, v___x_2372_);
v___x_2374_ = lean_string_append(v___x_2370_, v___x_2373_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3));
v___x_2376_ = lean_string_append(v___x_2374_, v___x_2375_);
v___x_2377_ = l_Lean_ConstantInfo_type(v_val_2365_);
lean_dec(v_val_2365_);
v___x_2378_ = lean_expr_dbg_to_string(v___x_2377_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = lean_string_append(v___x_2376_, v___x_2378_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2381_ = lean_string_append(v___x_2379_, v___x_2380_);
v___x_2382_ = lean_mk_io_user_error(v___x_2381_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2382_);
v___x_2384_ = v___x_2367_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(lean_object* v_declName_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2411_, v_a_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(lean_object* v_e_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_declName_2418_; lean_object* v___x_2419_; 
v_declName_2418_ = lean_ctor_get(v_e_2415_, 0);
lean_inc(v_declName_2418_);
v___x_2419_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2418_, v_a_2416_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2428_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2428_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_e_2415_);
lean_ctor_set(v___x_2424_, 1, v_a_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2424_);
v___x_2426_ = v___x_2422_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v_e_2415_);
v_a_2429_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2419_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2419_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(lean_object* v_e_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_2437_, v_a_2438_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3, &l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3);
v___x_2443_ = lean_st_mk_ref(v___x_2442_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___y_2447_){
_start:
{
lean_inc_ref(v___y_2447_);
return v___y_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___y_2448_);
lean_dec_ref(v___y_2448_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_x_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v___y_2451_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_2455_, v___y_2456_, v___y_2457_);
lean_dec_ref(v_x_2455_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_e_2460_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2461_; 
v_toCbvSimprocOLeanEntry_2461_ = lean_ctor_get(v_e_2460_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2461_);
return v_toCbvSimprocOLeanEntry_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_e_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_e_2462_);
lean_dec_ref(v_e_2462_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v_s_2464_, lean_object* v_e_2465_){
_start:
{
lean_object* v_toCbvSimprocOLeanEntry_2466_; lean_object* v_proc_2467_; lean_object* v_declName_2468_; uint8_t v_phase_2469_; lean_object* v_keys_2470_; lean_object* v___x_2471_; 
v_toCbvSimprocOLeanEntry_2466_ = lean_ctor_get(v_e_2465_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_2466_);
v_proc_2467_ = lean_ctor_get(v_e_2465_, 1);
lean_inc_ref(v_proc_2467_);
lean_dec_ref(v_e_2465_);
v_declName_2468_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2466_, 0);
lean_inc(v_declName_2468_);
v_phase_2469_ = lean_ctor_get_uint8(v_toCbvSimprocOLeanEntry_2466_, sizeof(void*)*2);
v_keys_2470_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_2466_, 1);
lean_inc_ref(v_keys_2470_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_2466_);
v___x_2471_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v_s_2464_, v_keys_2470_, v_declName_2468_, v_phase_2469_, v_proc_2467_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(uint8_t v_x_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___y_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_x_2475_, lean_object* v___y_2476_){
_start:
{
uint8_t v_x_126__boxed_2477_; lean_object* v_res_2478_; 
v_x_126__boxed_2477_ = lean_unbox(v_x_2475_);
v_res_2478_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_126__boxed_2477_, v___y_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(lean_object* v___x_2479_){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_st_ref_get(v___x_2479_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v___x_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_2483_);
lean_dec(v___x_2483_);
return v_res_2485_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___f_2495_; 
v___x_2494_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___f_2495_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_2495_, 0, v___x_2494_);
return v___f_2495_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_2496_; lean_object* v___f_2497_; lean_object* v___f_2498_; lean_object* v___f_2499_; lean_object* v___f_2500_; lean_object* v___f_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___f_2496_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2497_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2498_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2499_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2500_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___f_2501_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2502_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_));
v___x_2503_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___f_2501_);
lean_ctor_set(v___x_2503_, 2, v___f_2500_);
lean_ctor_set(v___x_2503_, 3, v___f_2499_);
lean_ctor_set(v___x_2503_, 4, v___f_2498_);
lean_ctor_set(v___x_2503_, 5, v___f_2497_);
lean_ctor_set(v___x_2503_, 6, v___f_2496_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_, &l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once, _init_l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
v___x_2506_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(lean_object* v_declName_2509_, lean_object* v_s_2510_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(v_s_2510_, v_declName_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2512_, lean_object* v_i_2513_, lean_object* v_k_2514_){
_start:
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = lean_array_get_size(v_keys_2512_);
v___x_2516_ = lean_nat_dec_lt(v_i_2513_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_dec(v_i_2513_);
return v___x_2516_;
}
else
{
lean_object* v_k_x27_2517_; uint8_t v___x_2518_; 
v_k_x27_2517_ = lean_array_fget_borrowed(v_keys_2512_, v_i_2513_);
v___x_2518_ = lean_name_eq(v_k_2514_, v_k_x27_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_unsigned_to_nat(1u);
v___x_2520_ = lean_nat_add(v_i_2513_, v___x_2519_);
lean_dec(v_i_2513_);
v_i_2513_ = v___x_2520_;
goto _start;
}
else
{
lean_dec(v_i_2513_);
return v___x_2518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2522_, lean_object* v_i_2523_, lean_object* v_k_2524_){
_start:
{
uint8_t v_res_2525_; lean_object* v_r_2526_; 
v_res_2525_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2522_, v_i_2523_, v_k_2524_);
lean_dec(v_k_2524_);
lean_dec_ref(v_keys_2522_);
v_r_2526_ = lean_box(v_res_2525_);
return v_r_2526_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(lean_object* v_x_2527_, size_t v_x_2528_, lean_object* v_x_2529_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 0)
{
lean_object* v_es_2530_; lean_object* v___x_2531_; size_t v___x_2532_; size_t v___x_2533_; size_t v___x_2534_; lean_object* v_j_2535_; lean_object* v___x_2536_; 
v_es_2530_ = lean_ctor_get(v_x_2527_, 0);
lean_inc_ref(v_es_2530_);
lean_dec_ref(v_x_2527_);
v___x_2531_ = lean_box(2);
v___x_2532_ = ((size_t)5ULL);
v___x_2533_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
v___x_2534_ = lean_usize_land(v_x_2528_, v___x_2533_);
v_j_2535_ = lean_usize_to_nat(v___x_2534_);
v___x_2536_ = lean_array_get(v___x_2531_, v_es_2530_, v_j_2535_);
lean_dec(v_j_2535_);
lean_dec_ref(v_es_2530_);
switch(lean_obj_tag(v___x_2536_))
{
case 0:
{
lean_object* v_key_2537_; uint8_t v___x_2538_; 
v_key_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_key_2537_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = lean_name_eq(v_x_2529_, v_key_2537_);
lean_dec(v_key_2537_);
return v___x_2538_;
}
case 1:
{
lean_object* v_node_2539_; size_t v___x_2540_; 
v_node_2539_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_node_2539_);
lean_dec_ref(v___x_2536_);
v___x_2540_ = lean_usize_shift_right(v_x_2528_, v___x_2532_);
v_x_2527_ = v_node_2539_;
v_x_2528_ = v___x_2540_;
goto _start;
}
default: 
{
uint8_t v___x_2542_; 
v___x_2542_ = 0;
return v___x_2542_;
}
}
}
else
{
lean_object* v_ks_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_ks_2543_ = lean_ctor_get(v_x_2527_, 0);
lean_inc_ref(v_ks_2543_);
lean_dec_ref(v_x_2527_);
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_2543_, v___x_2544_, v_x_2529_);
lean_dec_ref(v_ks_2543_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_){
_start:
{
size_t v_x_558__boxed_2549_; uint8_t v_res_2550_; lean_object* v_r_2551_; 
v_x_558__boxed_2549_ = lean_unbox_usize(v_x_2547_);
lean_dec(v_x_2547_);
v_res_2550_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2546_, v_x_558__boxed_2549_, v_x_2548_);
lean_dec(v_x_2548_);
v_r_2551_ = lean_box(v_res_2550_);
return v_r_2551_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(lean_object* v_x_2552_, lean_object* v_x_2553_){
_start:
{
uint64_t v___y_2555_; 
if (lean_obj_tag(v_x_2553_) == 0)
{
uint64_t v___x_2558_; 
v___x_2558_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2555_ = v___x_2558_;
goto v___jp_2554_;
}
else
{
uint64_t v_hash_2559_; 
v_hash_2559_ = lean_ctor_get_uint64(v_x_2553_, sizeof(void*)*2);
v___y_2555_ = v_hash_2559_;
goto v___jp_2554_;
}
v___jp_2554_:
{
size_t v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = lean_uint64_to_usize(v___y_2555_);
v___x_2557_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2552_, v___x_2556_, v_x_2553_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(lean_object* v_x_2560_, lean_object* v_x_2561_){
_start:
{
uint8_t v_res_2562_; lean_object* v_r_2563_; 
v_res_2562_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2560_, v_x_2561_);
lean_dec(v_x_2561_);
v_r_2563_ = lean_box(v_res_2562_);
return v_r_2563_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1));
v___x_2565_ = l_Lean_stringToMessageData(v___x_2564_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1));
v___x_2568_ = l_Lean_stringToMessageData(v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(lean_object* v_declName_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; lean_object* v_env_2574_; lean_object* v___x_2575_; lean_object* v_ext_2576_; lean_object* v_toEnvExtension_2577_; lean_object* v_asyncMode_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v_simprocNames_2581_; lean_object* v___f_2582_; lean_object* v___y_2584_; uint8_t v___x_2607_; 
v___x_2573_ = lean_st_ref_get(v_a_2571_);
v_env_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc_ref(v_env_2574_);
lean_dec(v___x_2573_);
v___x_2575_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_2576_ = lean_ctor_get(v___x_2575_, 1);
lean_inc_ref(v_ext_2576_);
v_toEnvExtension_2577_ = lean_ctor_get(v_ext_2576_, 0);
lean_inc_ref(v_toEnvExtension_2577_);
lean_dec_ref(v_ext_2576_);
v_asyncMode_2578_ = lean_ctor_get(v_toEnvExtension_2577_, 2);
lean_inc(v_asyncMode_2578_);
lean_dec_ref(v_toEnvExtension_2577_);
v___x_2579_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_2580_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2579_, v___x_2575_, v_env_2574_, v_asyncMode_2578_);
lean_dec(v_asyncMode_2578_);
v_simprocNames_2581_ = lean_ctor_get(v___x_2580_, 3);
lean_inc_ref(v_simprocNames_2581_);
lean_dec(v___x_2580_);
lean_inc(v_declName_2569_);
v___f_2582_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0), 2, 1);
lean_closure_set(v___f_2582_, 0, v_declName_2569_);
v___x_2607_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_simprocNames_2581_, v_declName_2569_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v___f_2582_);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; lean_object* v_unused_2621_; 
v_unused_2620_ = lean_ctor_get(v___x_2575_, 1);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v___x_2575_, 0);
lean_dec(v_unused_2621_);
v___x_2609_ = v___x_2575_;
v_isShared_2610_ = v_isSharedCheck_2619_;
goto v_resetjp_2608_;
}
else
{
lean_dec(v___x_2575_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2619_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2611_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0);
v___x_2612_ = l_Lean_MessageData_ofConstName(v_declName_2569_, v___x_2607_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 7);
lean_ctor_set(v___x_2609_, 1, v___x_2612_);
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2614_ = v___x_2609_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2616_, v_a_2570_, v_a_2571_);
return v___x_2617_;
}
}
}
else
{
lean_dec(v_declName_2569_);
v___y_2584_ = v_a_2571_;
goto v___jp_2583_;
}
v___jp_2583_:
{
lean_object* v___x_2585_; lean_object* v_env_2586_; lean_object* v_nextMacroScope_2587_; lean_object* v_ngen_2588_; lean_object* v_auxDeclNGen_2589_; lean_object* v_traceState_2590_; lean_object* v_messages_2591_; lean_object* v_infoState_2592_; lean_object* v_snapshotTasks_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2605_; 
v___x_2585_ = lean_st_ref_take(v___y_2584_);
v_env_2586_ = lean_ctor_get(v___x_2585_, 0);
v_nextMacroScope_2587_ = lean_ctor_get(v___x_2585_, 1);
v_ngen_2588_ = lean_ctor_get(v___x_2585_, 2);
v_auxDeclNGen_2589_ = lean_ctor_get(v___x_2585_, 3);
v_traceState_2590_ = lean_ctor_get(v___x_2585_, 4);
v_messages_2591_ = lean_ctor_get(v___x_2585_, 6);
v_infoState_2592_ = lean_ctor_get(v___x_2585_, 7);
v_snapshotTasks_2593_ = lean_ctor_get(v___x_2585_, 8);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2585_, 5);
lean_dec(v_unused_2606_);
v___x_2595_ = v___x_2585_;
v_isShared_2596_ = v_isSharedCheck_2605_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_snapshotTasks_2593_);
lean_inc(v_infoState_2592_);
lean_inc(v_messages_2591_);
lean_inc(v_traceState_2590_);
lean_inc(v_auxDeclNGen_2589_);
lean_inc(v_ngen_2588_);
lean_inc(v_nextMacroScope_2587_);
lean_inc(v_env_2586_);
lean_dec(v___x_2585_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2605_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_2575_, v_env_2586_, v___f_2582_);
v___x_2598_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 5, v___x_2598_);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_nextMacroScope_2587_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_ngen_2588_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_auxDeclNGen_2589_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_traceState_2590_);
lean_ctor_set(v_reuseFailAlloc_2604_, 5, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2604_, 6, v_messages_2591_);
lean_ctor_set(v_reuseFailAlloc_2604_, 7, v_infoState_2592_);
lean_ctor_set(v_reuseFailAlloc_2604_, 8, v_snapshotTasks_2593_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_st_ref_set(v___y_2584_, v___x_2600_);
v___x_2602_ = lean_box(0);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(lean_object* v_declName_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
return v_res_2626_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(lean_object* v_00_u03b2_2627_, lean_object* v_x_2628_, lean_object* v_x_2629_){
_start:
{
uint8_t v___x_2630_; 
v___x_2630_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_2628_, v_x_2629_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(lean_object* v_00_u03b2_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_){
_start:
{
uint8_t v_res_2634_; lean_object* v_r_2635_; 
v_res_2634_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(v_00_u03b2_2631_, v_x_2632_, v_x_2633_);
lean_dec(v_x_2633_);
v_r_2635_ = lean_box(v_res_2634_);
return v_r_2635_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(lean_object* v_00_u03b2_2636_, lean_object* v_x_2637_, size_t v_x_2638_, lean_object* v_x_2639_){
_start:
{
uint8_t v___x_2640_; 
v___x_2640_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_2637_, v_x_2638_, v_x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
size_t v_x_733__boxed_2645_; uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_x_733__boxed_2645_ = lean_unbox_usize(v_x_2643_);
lean_dec(v_x_2643_);
v_res_2646_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(v_00_u03b2_2641_, v_x_2642_, v_x_733__boxed_2645_, v_x_2644_);
lean_dec(v_x_2644_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2648_, lean_object* v_keys_2649_, lean_object* v_vals_2650_, lean_object* v_heq_2651_, lean_object* v_i_2652_, lean_object* v_k_2653_){
_start:
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_2649_, v_i_2652_, v_k_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2655_, lean_object* v_keys_2656_, lean_object* v_vals_2657_, lean_object* v_heq_2658_, lean_object* v_i_2659_, lean_object* v_k_2660_){
_start:
{
uint8_t v_res_2661_; lean_object* v_r_2662_; 
v_res_2661_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_2655_, v_keys_2656_, v_vals_2657_, v_heq_2658_, v_i_2659_, v_k_2660_);
lean_dec(v_k_2660_);
lean_dec_ref(v_vals_2657_);
lean_dec_ref(v_keys_2656_);
v_r_2662_ = lean_box(v_res_2661_);
return v_r_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(lean_object* v_ext_2663_, lean_object* v_b_2664_, uint8_t v_kind_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_currNamespace_2669_; lean_object* v___x_2670_; lean_object* v_env_2671_; lean_object* v_nextMacroScope_2672_; lean_object* v_ngen_2673_; lean_object* v_auxDeclNGen_2674_; lean_object* v_traceState_2675_; lean_object* v_messages_2676_; lean_object* v_infoState_2677_; lean_object* v_snapshotTasks_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2690_; 
v_currNamespace_2669_ = lean_ctor_get(v___y_2666_, 6);
lean_inc(v_currNamespace_2669_);
lean_dec_ref(v___y_2666_);
v___x_2670_ = lean_st_ref_take(v___y_2667_);
v_env_2671_ = lean_ctor_get(v___x_2670_, 0);
v_nextMacroScope_2672_ = lean_ctor_get(v___x_2670_, 1);
v_ngen_2673_ = lean_ctor_get(v___x_2670_, 2);
v_auxDeclNGen_2674_ = lean_ctor_get(v___x_2670_, 3);
v_traceState_2675_ = lean_ctor_get(v___x_2670_, 4);
v_messages_2676_ = lean_ctor_get(v___x_2670_, 6);
v_infoState_2677_ = lean_ctor_get(v___x_2670_, 7);
v_snapshotTasks_2678_ = lean_ctor_get(v___x_2670_, 8);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v___x_2670_, 5);
lean_dec(v_unused_2691_);
v___x_2680_ = v___x_2670_;
v_isShared_2681_ = v_isSharedCheck_2690_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_snapshotTasks_2678_);
lean_inc(v_infoState_2677_);
lean_inc(v_messages_2676_);
lean_inc(v_traceState_2675_);
lean_inc(v_auxDeclNGen_2674_);
lean_inc(v_ngen_2673_);
lean_inc(v_nextMacroScope_2672_);
lean_inc(v_env_2671_);
lean_dec(v___x_2670_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2690_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2682_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_2671_, v_ext_2663_, v_b_2664_, v_kind_2665_, v_currNamespace_2669_);
v___x_2683_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2, &l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 5, v___x_2683_);
lean_ctor_set(v___x_2680_, 0, v___x_2682_);
v___x_2685_ = v___x_2680_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_nextMacroScope_2672_);
lean_ctor_set(v_reuseFailAlloc_2689_, 2, v_ngen_2673_);
lean_ctor_set(v_reuseFailAlloc_2689_, 3, v_auxDeclNGen_2674_);
lean_ctor_set(v_reuseFailAlloc_2689_, 4, v_traceState_2675_);
lean_ctor_set(v_reuseFailAlloc_2689_, 5, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2689_, 6, v_messages_2676_);
lean_ctor_set(v_reuseFailAlloc_2689_, 7, v_infoState_2677_);
lean_ctor_set(v_reuseFailAlloc_2689_, 8, v_snapshotTasks_2678_);
v___x_2685_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_st_ref_set(v___y_2667_, v___x_2685_);
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
return v___x_2688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(lean_object* v_ext_2692_, lean_object* v_b_2693_, lean_object* v_kind_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v_kind_boxed_2698_; lean_object* v_res_2699_; 
v_kind_boxed_2698_ = lean_unbox(v_kind_2694_);
v_res_2699_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2692_, v_b_2693_, v_kind_boxed_2698_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(lean_object* v_00_u03b1_2700_, lean_object* v_00_u03b2_2701_, lean_object* v_00_u03c3_2702_, lean_object* v_ext_2703_, lean_object* v_b_2704_, uint8_t v_kind_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_2703_, v_b_2704_, v_kind_2705_, v___y_2706_, v___y_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(lean_object* v_00_u03b1_2710_, lean_object* v_00_u03b2_2711_, lean_object* v_00_u03c3_2712_, lean_object* v_ext_2713_, lean_object* v_b_2714_, lean_object* v_kind_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v_kind_boxed_2719_; lean_object* v_res_2720_; 
v_kind_boxed_2719_ = lean_unbox(v_kind_2715_);
v_res_2720_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(v_00_u03b1_2710_, v_00_u03b2_2711_, v_00_u03c3_2712_, v_ext_2713_, v_b_2714_, v_kind_boxed_2719_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
return v_res_2720_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0));
v___x_2723_ = l_Lean_stringToMessageData(v___x_2722_);
return v___x_2723_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2));
v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(lean_object* v_declName_2727_, uint8_t v_kind_2728_, uint8_t v_phase_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v___x_2733_; lean_object* v_env_2734_; lean_object* v_options_2735_; lean_object* v_ref_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2733_ = lean_st_ref_get(v_a_2731_);
v_env_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc_ref(v_env_2734_);
lean_dec(v___x_2733_);
v_options_2735_ = lean_ctor_get(v_a_2730_, 2);
v_ref_2736_ = lean_ctor_get(v_a_2730_, 5);
lean_inc_ref(v_options_2735_);
v___x_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2737_, 0, v_env_2734_);
lean_ctor_set(v___x_2737_, 1, v_options_2735_);
lean_inc(v_declName_2727_);
v___x_2738_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_2727_, v___x_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2740_; lean_object* v_a_2741_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref(v___x_2738_);
lean_inc(v_declName_2727_);
v___x_2740_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_2727_, v_a_2731_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2740_);
if (lean_obj_tag(v_a_2741_) == 1)
{
lean_object* v_val_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_val_2742_ = lean_ctor_get(v_a_2741_, 0);
lean_inc(v_val_2742_);
lean_dec_ref(v_a_2741_);
v___x_2743_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v___x_2744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2744_, 0, v_declName_2727_);
lean_ctor_set(v___x_2744_, 1, v_val_2742_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*2, v_phase_2729_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v_a_2739_);
v___x_2746_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v___x_2743_, v___x_2745_, v_kind_2728_, v_a_2730_, v_a_2731_);
return v___x_2746_;
}
else
{
lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_dec(v_a_2741_);
lean_dec(v_a_2739_);
v___x_2747_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1);
v___x_2748_ = 0;
v___x_2749_ = l_Lean_MessageData_ofConstName(v_declName_2727_, v___x_2748_);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2747_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_2752_, v_a_2730_, v_a_2731_);
lean_dec_ref(v_a_2730_);
return v___x_2753_;
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2765_; 
lean_inc(v_ref_2736_);
lean_dec_ref(v_a_2730_);
lean_dec(v_declName_2727_);
v_a_2754_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2756_ = v___x_2738_;
v_isShared_2757_ = v_isSharedCheck_2765_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2738_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2765_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2758_ = lean_io_error_to_string(v_a_2754_);
v___x_2759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
v___x_2760_ = l_Lean_MessageData_ofFormat(v___x_2759_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_ref_2736_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2761_);
v___x_2763_ = v___x_2756_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(lean_object* v_declName_2766_, lean_object* v_kind_2767_, lean_object* v_phase_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
uint8_t v_kind_boxed_2772_; uint8_t v_phase_boxed_2773_; lean_object* v_res_2774_; 
v_kind_boxed_2772_ = lean_unbox(v_kind_2767_);
v_phase_boxed_2773_ = lean_unbox(v_phase_2768_);
v_res_2774_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2766_, v_kind_boxed_2772_, v_phase_boxed_2773_, v_a_2769_, v_a_2770_);
lean_dec(v_a_2770_);
return v_res_2774_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(lean_object* v_stx_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = l_Lean_Syntax_isNone(v_stx_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v_inner_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2789_ = lean_unsigned_to_nat(0u);
v_inner_2790_ = l_Lean_Syntax_getArg(v_stx_2787_, v___x_2789_);
v___x_2791_ = l_Lean_Syntax_getKind(v_inner_2790_);
v___x_2792_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2));
v___x_2793_ = lean_name_eq(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; uint8_t v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4));
v___x_2795_ = lean_name_eq(v___x_2791_, v___x_2794_);
lean_dec(v___x_2791_);
if (v___x_2795_ == 0)
{
uint8_t v___x_2796_; 
v___x_2796_ = 2;
return v___x_2796_;
}
else
{
uint8_t v___x_2797_; 
v___x_2797_ = 1;
return v___x_2797_;
}
}
else
{
uint8_t v___x_2798_; 
lean_dec(v___x_2791_);
v___x_2798_ = 0;
return v___x_2798_;
}
}
else
{
uint8_t v___x_2799_; 
v___x_2799_ = 2;
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(lean_object* v_stx_2800_){
_start:
{
uint8_t v_res_2801_; lean_object* v_r_2802_; 
v_res_2801_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_2800_);
lean_dec(v_stx_2800_);
v_r_2802_ = lean_box(v_res_2801_);
return v_r_2802_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
lean_ctor_set(v___x_2807_, 2, v___x_2806_);
lean_ctor_set(v___x_2807_, 3, v___x_2806_);
lean_ctor_set(v___x_2807_, 4, v___x_2806_);
lean_ctor_set(v___x_2807_, 5, v___x_2806_);
return v___x_2807_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = lean_unsigned_to_nat(32u);
v___x_2809_ = lean_mk_empty_array_with_capacity(v___x_2808_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4(void){
_start:
{
size_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2811_ = ((size_t)5ULL);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = lean_unsigned_to_nat(32u);
v___x_2814_ = lean_mk_empty_array_with_capacity(v___x_2813_);
v___x_2815_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3);
v___x_2816_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v___x_2814_);
lean_ctor_set(v___x_2816_, 2, v___x_2812_);
lean_ctor_set(v___x_2816_, 3, v___x_2812_);
lean_ctor_set_usize(v___x_2816_, 4, v___x_2811_);
return v___x_2816_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
v___x_2818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
lean_ctor_set(v___x_2818_, 2, v___x_2817_);
lean_ctor_set(v___x_2818_, 3, v___x_2817_);
lean_ctor_set(v___x_2818_, 4, v___x_2817_);
return v___x_2818_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2819_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5);
v___x_2820_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4);
v___x_2821_ = lean_box(1);
v___x_2822_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2);
v___x_2823_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
v___x_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
lean_ctor_set(v___x_2824_, 1, v___x_2822_);
lean_ctor_set(v___x_2824_, 2, v___x_2821_);
lean_ctor_set(v___x_2824_, 3, v___x_2820_);
lean_ctor_set(v___x_2824_, 4, v___x_2819_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(lean_object* v_declName_2825_, lean_object* v_stx_2826_, uint8_t v_attrKind_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1));
lean_inc(v_a_2829_);
lean_inc_ref(v_a_2828_);
lean_inc(v_declName_2825_);
v___x_2832_ = l_Lean_ensureAttrDeclIsMeta(v___x_2831_, v_declName_2825_, v_attrKind_2827_, v_a_2828_, v_a_2829_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; 
lean_dec_ref(v___x_2832_);
v___x_2833_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_2834_ = lean_st_mk_ref(v___x_2833_);
v___x_2835_ = lean_unsigned_to_nat(1u);
v___x_2836_ = l_Lean_Syntax_getArg(v_stx_2826_, v___x_2835_);
v___x_2837_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_2836_);
lean_dec(v___x_2836_);
v___x_2838_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(v_declName_2825_, v_attrKind_2827_, v___x_2837_, v_a_2828_, v_a_2829_);
lean_dec(v_a_2829_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2847_; 
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2838_, 0);
lean_dec(v_unused_2848_);
v___x_2840_ = v___x_2838_;
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2838_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2847_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2842_ = lean_st_ref_get(v___x_2834_);
lean_dec(v___x_2834_);
lean_dec(v___x_2842_);
v___x_2843_ = lean_box(0);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_dec(v___x_2834_);
return v___x_2838_;
}
}
else
{
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_declName_2825_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(lean_object* v_declName_2849_, lean_object* v_stx_2850_, lean_object* v_attrKind_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
uint8_t v_attrKind_boxed_2855_; lean_object* v_res_2856_; 
v_attrKind_boxed_2855_ = lean_unbox(v_attrKind_2851_);
v_res_2856_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(v_declName_2849_, v_stx_2850_, v_attrKind_boxed_2855_, v_a_2852_, v_a_2853_);
lean_dec(v_stx_2850_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(lean_object* v_ref_2859_, lean_object* v_declName_2860_, uint8_t v_phase_2861_, lean_object* v_proc_2862_){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v_keys_2866_; lean_object* v___x_2867_; 
v___x_2864_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
v___x_2865_ = lean_st_ref_get(v___x_2864_);
v_keys_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc_ref(v_keys_2866_);
lean_dec(v___x_2865_);
v___x_2867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_keys_2866_, v_declName_2860_);
lean_dec_ref(v_keys_2866_);
if (lean_obj_tag(v___x_2867_) == 1)
{
lean_object* v_val_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2878_; 
v_val_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2878_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_val_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2878_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2872_ = lean_st_ref_take(v_ref_2859_);
v___x_2873_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(v___x_2872_, v_val_2868_, v_declName_2860_, v_phase_2861_, v_proc_2862_);
v___x_2874_ = lean_st_ref_set(v_ref_2859_, v___x_2873_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2874_);
v___x_2876_ = v___x_2870_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec(v___x_2867_);
lean_dec_ref(v_proc_2862_);
v___x_2879_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0));
v___x_2880_ = l_Lean_privateToUserName(v_declName_2860_);
v___x_2881_ = 1;
v___x_2882_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2880_, v___x_2881_);
v___x_2883_ = lean_string_append(v___x_2879_, v___x_2882_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1));
v___x_2885_ = lean_string_append(v___x_2883_, v___x_2884_);
v___x_2886_ = lean_mk_io_user_error(v___x_2885_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
return v___x_2887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(lean_object* v_ref_2888_, lean_object* v_declName_2889_, lean_object* v_phase_2890_, lean_object* v_proc_2891_, lean_object* v_a_2892_){
_start:
{
uint8_t v_phase_boxed_2893_; lean_object* v_res_2894_; 
v_phase_boxed_2893_ = lean_unbox(v_phase_2890_);
v_res_2894_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v_ref_2888_, v_declName_2889_, v_phase_boxed_2893_, v_proc_2891_);
lean_dec(v_ref_2888_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object* v_declName_2895_, uint8_t v_phase_2896_, lean_object* v_proc_2897_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
v___x_2900_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(v___x_2899_, v_declName_2895_, v_phase_2896_, v_proc_2897_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(lean_object* v_declName_2901_, lean_object* v_phase_2902_, lean_object* v_proc_2903_, lean_object* v_a_2904_){
_start:
{
uint8_t v_phase_boxed_2905_; lean_object* v_res_2906_; 
v_phase_boxed_2905_ = lean_unbox(v_phase_2902_);
v_res_2906_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v_declName_2901_, v_phase_boxed_2905_, v_proc_2903_);
return v_res_2906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_box(0);
v___x_2915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1));
v___x_2916_ = l_Lean_mkConst(v___x_2915_, v___x_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(lean_object* v_declName_2920_, lean_object* v_stx_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v_phase_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___y_2932_; 
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = l_Lean_Syntax_getArg(v_stx_2921_, v___x_2925_);
v_phase_2927_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_2926_);
lean_dec(v___x_2926_);
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2);
lean_inc(v_declName_2920_);
v___x_2930_ = l_Lean_instToExprName___private__1(v_declName_2920_);
switch(v_phase_2927_)
{
case 0:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
v___y_2932_ = v___x_2964_;
goto v___jp_2931_;
}
case 1:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
v___y_2932_ = v___x_2965_;
goto v___jp_2931_;
}
default: 
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13, &l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once, _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
v___y_2932_ = v___x_2966_;
goto v___jp_2931_;
}
}
v___jp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2933_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6, &l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6);
v___x_2934_ = lean_st_mk_ref(v___x_2933_);
lean_inc(v_declName_2920_);
v___x_2935_ = l_Lean_mkConst(v_declName_2920_, v___x_2928_);
v___x_2936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4));
v___x_2937_ = l_Lean_Name_append(v_declName_2920_, v___x_2936_);
lean_inc(v_a_2923_);
lean_inc_ref(v_a_2922_);
v___x_2938_ = l_Lean_Core_mkFreshUserName(v___x_2937_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_val_2945_; lean_object* v___x_2946_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = lean_unsigned_to_nat(3u);
v___x_2941_ = lean_mk_empty_array_with_capacity(v___x_2940_);
v___x_2942_ = lean_array_push(v___x_2941_, v___x_2930_);
v___x_2943_ = lean_array_push(v___x_2942_, v___y_2932_);
v___x_2944_ = lean_array_push(v___x_2943_, v___x_2935_);
v_val_2945_ = l_Lean_mkAppN(v___x_2929_, v___x_2944_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = l_Lean_declareBuiltin(v_a_2939_, v_val_2945_, v_a_2922_, v_a_2923_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2955_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2955_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2951_ = lean_st_ref_get(v___x_2934_);
lean_dec(v___x_2934_);
lean_dec(v___x_2951_);
if (v_isShared_2950_ == 0)
{
v___x_2953_ = v___x_2949_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2947_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
else
{
lean_dec(v___x_2934_);
return v___x_2946_;
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref(v___x_2935_);
lean_dec(v___x_2934_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v___x_2930_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
v_a_2956_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2938_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2938_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(lean_object* v_declName_2967_, lean_object* v_stx_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_2967_, v_stx_2968_, v_a_2969_, v_a_2970_);
lean_dec(v_stx_2968_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3059_ = l_Lean_registerBuiltinAttribute(v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_declName_3062_, lean_object* v_stx_3063_, uint8_t v_x_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(v_declName_3062_, v_stx_3063_, v___y_3065_, v___y_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_declName_3069_, lean_object* v_stx_3070_, lean_object* v_x_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
uint8_t v_x_116__boxed_3075_; lean_object* v_res_3076_; 
v_x_116__boxed_3075_ = lean_unbox(v_x_3071_);
v_res_3076_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_3069_, v_stx_3070_, v_x_116__boxed_3075_, v___y_3072_, v___y_3073_);
lean_dec(v_stx_3070_);
return v_res_3076_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(lean_object* v_x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3085_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_3084_, v___y_3081_, v___y_3082_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_x_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v_x_3086_);
return v_res_3090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_unsigned_to_nat(3124561870u);
v___x_3094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3095_ = l_Lean_Name_num___override(v___x_3094_, v___x_3093_);
return v___x_3095_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3098_ = l_Lean_Name_str___override(v___x_3097_, v___x_3096_);
return v___x_3098_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_));
v___x_3100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3101_ = l_Lean_Name_str___override(v___x_3100_, v___x_3099_);
return v___x_3101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_unsigned_to_nat(2u);
v___x_3103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3104_ = l_Lean_Name_num___override(v___x_3103_, v___x_3102_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3109_ = 1;
v___x_3110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v___x_3111_);
lean_ctor_set(v___x_3113_, 2, v___x_3110_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*3, v___x_3109_);
return v___x_3113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3114_; lean_object* v___f_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___f_3114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___f_3115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_));
v___x_3116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___f_3115_);
lean_ctor_set(v___x_3117_, 2, v___f_3114_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
v___x_3120_ = l_Lean_registerBuiltinAttribute(v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(lean_object* v_a_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object* v_a_3123_){
_start:
{
lean_object* v___x_3125_; lean_object* v_env_3126_; lean_object* v___x_3127_; lean_object* v_ext_3128_; lean_object* v_toEnvExtension_3129_; lean_object* v_asyncMode_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3125_ = lean_st_ref_get(v_a_3123_);
v_env_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc_ref(v_env_3126_);
lean_dec(v___x_3125_);
v___x_3127_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
v_ext_3128_ = lean_ctor_get(v___x_3127_, 1);
lean_inc_ref(v_ext_3128_);
v_toEnvExtension_3129_ = lean_ctor_get(v_ext_3128_, 0);
lean_inc_ref(v_toEnvExtension_3129_);
lean_dec_ref(v_ext_3128_);
v_asyncMode_3130_ = lean_ctor_get(v_toEnvExtension_3129_, 2);
lean_inc(v_asyncMode_3130_);
lean_dec_ref(v_toEnvExtension_3129_);
v___x_3131_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
v___x_3132_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3131_, v___x_3127_, v_env_3126_, v_asyncMode_3130_);
lean_dec(v_asyncMode_3130_);
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3134_);
lean_dec(v_a_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(lean_object* v_cls_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_options_3151_; uint8_t v_hasTrace_3152_; 
v_options_3151_ = lean_ctor_get(v___y_3149_, 2);
v_hasTrace_3152_ = lean_ctor_get_uint8(v_options_3151_, sizeof(void*)*1);
if (v_hasTrace_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec(v_cls_3148_);
v___x_3153_ = lean_box(v_hasTrace_3152_);
v___x_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
else
{
lean_object* v_inheritedTraceOptions_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v_inheritedTraceOptions_3155_ = lean_ctor_get(v___y_3149_, 13);
v___x_3156_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1));
v___x_3157_ = l_Lean_Name_append(v___x_3156_, v_cls_3148_);
v___x_3158_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3155_, v_options_3151_, v___x_3157_);
lean_dec(v___x_3157_);
v___x_3159_ = lean_box(v___x_3158_);
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(lean_object* v_cls_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v_cls_3161_, v___y_3162_);
lean_dec_ref(v___y_3162_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(lean_object* v_cls_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v_cls_3165_, v___y_3173_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(lean_object* v_cls_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v_cls_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
return v_res_3188_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_unsigned_to_nat(32u);
v___x_3190_ = lean_mk_empty_array_with_capacity(v___x_3189_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3192_ = ((size_t)5ULL);
v___x_3193_ = lean_unsigned_to_nat(0u);
v___x_3194_ = lean_unsigned_to_nat(32u);
v___x_3195_ = lean_mk_empty_array_with_capacity(v___x_3194_);
v___x_3196_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__0);
v___x_3197_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___x_3195_);
lean_ctor_set(v___x_3197_, 2, v___x_3193_);
lean_ctor_set(v___x_3197_, 3, v___x_3193_);
lean_ctor_set_usize(v___x_3197_, 4, v___x_3192_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg(lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v_traceState_3201_; lean_object* v_traces_3202_; lean_object* v___x_3203_; lean_object* v_traceState_3204_; lean_object* v_env_3205_; lean_object* v_nextMacroScope_3206_; lean_object* v_ngen_3207_; lean_object* v_auxDeclNGen_3208_; lean_object* v_cache_3209_; lean_object* v_messages_3210_; lean_object* v_infoState_3211_; lean_object* v_snapshotTasks_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3231_; 
v___x_3200_ = lean_st_ref_get(v___y_3198_);
v_traceState_3201_ = lean_ctor_get(v___x_3200_, 4);
lean_inc_ref(v_traceState_3201_);
lean_dec(v___x_3200_);
v_traces_3202_ = lean_ctor_get(v_traceState_3201_, 0);
lean_inc_ref(v_traces_3202_);
lean_dec_ref(v_traceState_3201_);
v___x_3203_ = lean_st_ref_take(v___y_3198_);
v_traceState_3204_ = lean_ctor_get(v___x_3203_, 4);
v_env_3205_ = lean_ctor_get(v___x_3203_, 0);
v_nextMacroScope_3206_ = lean_ctor_get(v___x_3203_, 1);
v_ngen_3207_ = lean_ctor_get(v___x_3203_, 2);
v_auxDeclNGen_3208_ = lean_ctor_get(v___x_3203_, 3);
v_cache_3209_ = lean_ctor_get(v___x_3203_, 5);
v_messages_3210_ = lean_ctor_get(v___x_3203_, 6);
v_infoState_3211_ = lean_ctor_get(v___x_3203_, 7);
v_snapshotTasks_3212_ = lean_ctor_get(v___x_3203_, 8);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3214_ = v___x_3203_;
v_isShared_3215_ = v_isSharedCheck_3231_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_snapshotTasks_3212_);
lean_inc(v_infoState_3211_);
lean_inc(v_messages_3210_);
lean_inc(v_cache_3209_);
lean_inc(v_traceState_3204_);
lean_inc(v_auxDeclNGen_3208_);
lean_inc(v_ngen_3207_);
lean_inc(v_nextMacroScope_3206_);
lean_inc(v_env_3205_);
lean_dec(v___x_3203_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3231_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint64_t v_tid_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3229_; 
v_tid_3216_ = lean_ctor_get_uint64(v_traceState_3204_, sizeof(void*)*1);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_traceState_3204_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v_traceState_3204_, 0);
lean_dec(v_unused_3230_);
v___x_3218_ = v_traceState_3204_;
v_isShared_3219_ = v_isSharedCheck_3229_;
goto v_resetjp_3217_;
}
else
{
lean_dec(v_traceState_3204_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3229_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___closed__1);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3220_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3220_);
lean_ctor_set_uint64(v_reuseFailAlloc_3228_, sizeof(void*)*1, v_tid_3216_);
v___x_3222_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3224_; 
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 4, v___x_3222_);
v___x_3224_ = v___x_3214_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_env_3205_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_nextMacroScope_3206_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_ngen_3207_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_auxDeclNGen_3208_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3227_, 5, v_cache_3209_);
lean_ctor_set(v_reuseFailAlloc_3227_, 6, v_messages_3210_);
lean_ctor_set(v_reuseFailAlloc_3227_, 7, v_infoState_3211_);
lean_ctor_set(v_reuseFailAlloc_3227_, 8, v_snapshotTasks_3212_);
v___x_3224_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = lean_st_ref_set(v___y_3198_, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v_traces_3202_);
return v___x_3226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg___boxed(lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg(v___y_3232_);
lean_dec(v___y_3232_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg(v___y_3243_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
return v_res_3256_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(lean_object* v_opts_3257_, lean_object* v_opt_3258_){
_start:
{
lean_object* v_name_3259_; lean_object* v_defValue_3260_; lean_object* v_map_3261_; lean_object* v___x_3262_; 
v_name_3259_ = lean_ctor_get(v_opt_3258_, 0);
v_defValue_3260_ = lean_ctor_get(v_opt_3258_, 1);
v_map_3261_ = lean_ctor_get(v_opts_3257_, 0);
v___x_3262_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3261_, v_name_3259_);
if (lean_obj_tag(v___x_3262_) == 0)
{
uint8_t v___x_3263_; 
v___x_3263_ = lean_unbox(v_defValue_3260_);
return v___x_3263_;
}
else
{
lean_object* v_val_3264_; 
v_val_3264_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_val_3264_);
lean_dec_ref(v___x_3262_);
if (lean_obj_tag(v_val_3264_) == 1)
{
uint8_t v_v_3265_; 
v_v_3265_ = lean_ctor_get_uint8(v_val_3264_, 0);
lean_dec_ref(v_val_3264_);
return v_v_3265_;
}
else
{
uint8_t v___x_3266_; 
lean_dec(v_val_3264_);
v___x_3266_ = lean_unbox(v_defValue_3260_);
return v___x_3266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(lean_object* v_opts_3267_, lean_object* v_opt_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_opts_3267_, v_opt_3268_);
lean_dec_ref(v_opt_3268_);
lean_dec_ref(v_opts_3267_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg(lean_object* v_x_3271_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
v_a_3273_ = lean_ctor_get(v_x_3271_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_x_3271_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v_x_3271_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v_x_3271_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 1);
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
v_a_3281_ = lean_ctor_get(v_x_3271_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_x_3271_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v_x_3271_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v_x_3271_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 0);
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg___boxed(lean_object* v_x_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg(v_x_3289_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__6(lean_object* v_msgData_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; lean_object* v_env_3299_; lean_object* v___x_3300_; lean_object* v_mctx_3301_; lean_object* v_lctx_3302_; lean_object* v_options_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3298_ = lean_st_ref_get(v___y_3296_);
v_env_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc_ref(v_env_3299_);
lean_dec(v___x_3298_);
v___x_3300_ = lean_st_ref_get(v___y_3294_);
v_mctx_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc_ref(v_mctx_3301_);
lean_dec(v___x_3300_);
v_lctx_3302_ = lean_ctor_get(v___y_3293_, 2);
v_options_3303_ = lean_ctor_get(v___y_3295_, 2);
lean_inc_ref(v_options_3303_);
lean_inc_ref(v_lctx_3302_);
v___x_3304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3304_, 0, v_env_3299_);
lean_ctor_set(v___x_3304_, 1, v_mctx_3301_);
lean_ctor_set(v___x_3304_, 2, v_lctx_3302_);
lean_ctor_set(v___x_3304_, 3, v_options_3303_);
v___x_3305_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v_msgData_3292_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__6___boxed(lean_object* v_msgData_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__6(v_msgData_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__5(size_t v_sz_3314_, size_t v_i_3315_, lean_object* v_bs_3316_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = lean_usize_dec_lt(v_i_3315_, v_sz_3314_);
if (v___x_3317_ == 0)
{
return v_bs_3316_;
}
else
{
lean_object* v_v_3318_; lean_object* v_msg_3319_; lean_object* v___x_3320_; lean_object* v_bs_x27_3321_; size_t v___x_3322_; size_t v___x_3323_; lean_object* v___x_3324_; 
v_v_3318_ = lean_array_uget_borrowed(v_bs_3316_, v_i_3315_);
v_msg_3319_ = lean_ctor_get(v_v_3318_, 1);
lean_inc_ref(v_msg_3319_);
v___x_3320_ = lean_unsigned_to_nat(0u);
v_bs_x27_3321_ = lean_array_uset(v_bs_3316_, v_i_3315_, v___x_3320_);
v___x_3322_ = ((size_t)1ULL);
v___x_3323_ = lean_usize_add(v_i_3315_, v___x_3322_);
v___x_3324_ = lean_array_uset(v_bs_x27_3321_, v_i_3315_, v_msg_3319_);
v_i_3315_ = v___x_3323_;
v_bs_3316_ = v___x_3324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_3326_, lean_object* v_i_3327_, lean_object* v_bs_3328_){
_start:
{
size_t v_sz_boxed_3329_; size_t v_i_boxed_3330_; lean_object* v_res_3331_; 
v_sz_boxed_3329_ = lean_unbox_usize(v_sz_3326_);
lean_dec(v_sz_3326_);
v_i_boxed_3330_ = lean_unbox_usize(v_i_3327_);
lean_dec(v_i_3327_);
v_res_3331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__5(v_sz_boxed_3329_, v_i_boxed_3330_, v_bs_3328_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___redArg(lean_object* v_oldTraces_3332_, lean_object* v_data_3333_, lean_object* v_ref_3334_, lean_object* v_msg_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_fileName_3341_; lean_object* v_fileMap_3342_; lean_object* v_options_3343_; lean_object* v_currRecDepth_3344_; lean_object* v_maxRecDepth_3345_; lean_object* v_ref_3346_; lean_object* v_currNamespace_3347_; lean_object* v_openDecls_3348_; lean_object* v_initHeartbeats_3349_; lean_object* v_maxHeartbeats_3350_; lean_object* v_quotContext_3351_; lean_object* v_currMacroScope_3352_; uint8_t v_diag_3353_; lean_object* v_cancelTk_x3f_3354_; uint8_t v_suppressElabErrors_3355_; lean_object* v_inheritedTraceOptions_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3411_; 
v_fileName_3341_ = lean_ctor_get(v___y_3338_, 0);
v_fileMap_3342_ = lean_ctor_get(v___y_3338_, 1);
v_options_3343_ = lean_ctor_get(v___y_3338_, 2);
v_currRecDepth_3344_ = lean_ctor_get(v___y_3338_, 3);
v_maxRecDepth_3345_ = lean_ctor_get(v___y_3338_, 4);
v_ref_3346_ = lean_ctor_get(v___y_3338_, 5);
v_currNamespace_3347_ = lean_ctor_get(v___y_3338_, 6);
v_openDecls_3348_ = lean_ctor_get(v___y_3338_, 7);
v_initHeartbeats_3349_ = lean_ctor_get(v___y_3338_, 8);
v_maxHeartbeats_3350_ = lean_ctor_get(v___y_3338_, 9);
v_quotContext_3351_ = lean_ctor_get(v___y_3338_, 10);
v_currMacroScope_3352_ = lean_ctor_get(v___y_3338_, 11);
v_diag_3353_ = lean_ctor_get_uint8(v___y_3338_, sizeof(void*)*14);
v_cancelTk_x3f_3354_ = lean_ctor_get(v___y_3338_, 12);
v_suppressElabErrors_3355_ = lean_ctor_get_uint8(v___y_3338_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3356_ = lean_ctor_get(v___y_3338_, 13);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___y_3338_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3358_ = v___y_3338_;
v_isShared_3359_ = v_isSharedCheck_3411_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_inheritedTraceOptions_3356_);
lean_inc(v_cancelTk_x3f_3354_);
lean_inc(v_currMacroScope_3352_);
lean_inc(v_quotContext_3351_);
lean_inc(v_maxHeartbeats_3350_);
lean_inc(v_initHeartbeats_3349_);
lean_inc(v_openDecls_3348_);
lean_inc(v_currNamespace_3347_);
lean_inc(v_ref_3346_);
lean_inc(v_maxRecDepth_3345_);
lean_inc(v_currRecDepth_3344_);
lean_inc(v_options_3343_);
lean_inc(v_fileMap_3342_);
lean_inc(v_fileName_3341_);
lean_dec(v___y_3338_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3411_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v_traceState_3361_; lean_object* v_traces_3362_; lean_object* v_ref_3363_; lean_object* v___x_3365_; 
v___x_3360_ = lean_st_ref_get(v___y_3339_);
v_traceState_3361_ = lean_ctor_get(v___x_3360_, 4);
lean_inc_ref(v_traceState_3361_);
lean_dec(v___x_3360_);
v_traces_3362_ = lean_ctor_get(v_traceState_3361_, 0);
lean_inc_ref(v_traces_3362_);
lean_dec_ref(v_traceState_3361_);
v_ref_3363_ = l_Lean_replaceRef(v_ref_3334_, v_ref_3346_);
lean_dec(v_ref_3346_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 5, v_ref_3363_);
v___x_3365_ = v___x_3358_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_fileName_3341_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_fileMap_3342_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_options_3343_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_currRecDepth_3344_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_maxRecDepth_3345_);
lean_ctor_set(v_reuseFailAlloc_3410_, 5, v_ref_3363_);
lean_ctor_set(v_reuseFailAlloc_3410_, 6, v_currNamespace_3347_);
lean_ctor_set(v_reuseFailAlloc_3410_, 7, v_openDecls_3348_);
lean_ctor_set(v_reuseFailAlloc_3410_, 8, v_initHeartbeats_3349_);
lean_ctor_set(v_reuseFailAlloc_3410_, 9, v_maxHeartbeats_3350_);
lean_ctor_set(v_reuseFailAlloc_3410_, 10, v_quotContext_3351_);
lean_ctor_set(v_reuseFailAlloc_3410_, 11, v_currMacroScope_3352_);
lean_ctor_set(v_reuseFailAlloc_3410_, 12, v_cancelTk_x3f_3354_);
lean_ctor_set(v_reuseFailAlloc_3410_, 13, v_inheritedTraceOptions_3356_);
lean_ctor_set_uint8(v_reuseFailAlloc_3410_, sizeof(void*)*14, v_diag_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3410_, sizeof(void*)*14 + 1, v_suppressElabErrors_3355_);
v___x_3365_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; size_t v_sz_3367_; size_t v___x_3368_; lean_object* v___x_3369_; lean_object* v_msg_3370_; lean_object* v___x_3371_; lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3409_; 
v___x_3366_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3362_);
lean_dec_ref(v_traces_3362_);
v_sz_3367_ = lean_array_size(v___x_3366_);
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__5(v_sz_3367_, v___x_3368_, v___x_3366_);
v_msg_3370_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3370_, 0, v_data_3333_);
lean_ctor_set(v_msg_3370_, 1, v_msg_3335_);
lean_ctor_set(v_msg_3370_, 2, v___x_3369_);
v___x_3371_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4_spec__6(v_msg_3370_, v___y_3336_, v___y_3337_, v___x_3365_, v___y_3339_);
lean_dec_ref(v___x_3365_);
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3409_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3409_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v_traceState_3377_; lean_object* v_env_3378_; lean_object* v_nextMacroScope_3379_; lean_object* v_ngen_3380_; lean_object* v_auxDeclNGen_3381_; lean_object* v_cache_3382_; lean_object* v_messages_3383_; lean_object* v_infoState_3384_; lean_object* v_snapshotTasks_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3408_; 
v___x_3376_ = lean_st_ref_take(v___y_3339_);
v_traceState_3377_ = lean_ctor_get(v___x_3376_, 4);
v_env_3378_ = lean_ctor_get(v___x_3376_, 0);
v_nextMacroScope_3379_ = lean_ctor_get(v___x_3376_, 1);
v_ngen_3380_ = lean_ctor_get(v___x_3376_, 2);
v_auxDeclNGen_3381_ = lean_ctor_get(v___x_3376_, 3);
v_cache_3382_ = lean_ctor_get(v___x_3376_, 5);
v_messages_3383_ = lean_ctor_get(v___x_3376_, 6);
v_infoState_3384_ = lean_ctor_get(v___x_3376_, 7);
v_snapshotTasks_3385_ = lean_ctor_get(v___x_3376_, 8);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3387_ = v___x_3376_;
v_isShared_3388_ = v_isSharedCheck_3408_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_snapshotTasks_3385_);
lean_inc(v_infoState_3384_);
lean_inc(v_messages_3383_);
lean_inc(v_cache_3382_);
lean_inc(v_traceState_3377_);
lean_inc(v_auxDeclNGen_3381_);
lean_inc(v_ngen_3380_);
lean_inc(v_nextMacroScope_3379_);
lean_inc(v_env_3378_);
lean_dec(v___x_3376_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3408_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
uint64_t v_tid_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3406_; 
v_tid_3389_ = lean_ctor_get_uint64(v_traceState_3377_, sizeof(void*)*1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_traceState_3377_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_traceState_3377_, 0);
lean_dec(v_unused_3407_);
v___x_3391_ = v_traceState_3377_;
v_isShared_3392_ = v_isSharedCheck_3406_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v_traceState_3377_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3406_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v_ref_3334_);
lean_ctor_set(v___x_3393_, 1, v_a_3372_);
v___x_3394_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3332_, v___x_3393_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3394_);
v___x_3396_ = v___x_3391_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3394_);
lean_ctor_set_uint64(v_reuseFailAlloc_3405_, sizeof(void*)*1, v_tid_3389_);
v___x_3396_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v___x_3396_);
v___x_3398_ = v___x_3387_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_env_3378_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_nextMacroScope_3379_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_ngen_3380_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_auxDeclNGen_3381_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3404_, 5, v_cache_3382_);
lean_ctor_set(v_reuseFailAlloc_3404_, 6, v_messages_3383_);
lean_ctor_set(v_reuseFailAlloc_3404_, 7, v_infoState_3384_);
lean_ctor_set(v_reuseFailAlloc_3404_, 8, v_snapshotTasks_3385_);
v___x_3398_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3399_ = lean_st_ref_set(v___y_3339_, v___x_3398_);
v___x_3400_ = lean_box(0);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3400_);
v___x_3402_ = v___x_3374_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_3412_, lean_object* v_data_3413_, lean_object* v_ref_3414_, lean_object* v_msg_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___redArg(v_oldTraces_3412_, v_data_3413_, v_ref_3414_, v_msg_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
return v_res_3421_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__3(lean_object* v_e_3422_){
_start:
{
if (lean_obj_tag(v_e_3422_) == 0)
{
uint8_t v___x_3423_; 
v___x_3423_ = 2;
return v___x_3423_;
}
else
{
uint8_t v___x_3424_; 
v___x_3424_ = 0;
return v___x_3424_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__3___boxed(lean_object* v_e_3425_){
_start:
{
uint8_t v_res_3426_; lean_object* v_r_3427_; 
v_res_3426_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__3(v_e_3425_);
lean_dec_ref(v_e_3425_);
v_r_3427_ = lean_box(v_res_3426_);
return v_r_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__6(lean_object* v_opts_3428_, lean_object* v_opt_3429_){
_start:
{
lean_object* v_name_3430_; lean_object* v_defValue_3431_; lean_object* v_map_3432_; lean_object* v___x_3433_; 
v_name_3430_ = lean_ctor_get(v_opt_3429_, 0);
v_defValue_3431_ = lean_ctor_get(v_opt_3429_, 1);
v_map_3432_ = lean_ctor_get(v_opts_3428_, 0);
v___x_3433_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3432_, v_name_3430_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_inc(v_defValue_3431_);
return v_defValue_3431_;
}
else
{
lean_object* v_val_3434_; 
v_val_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_val_3434_);
lean_dec_ref(v___x_3433_);
if (lean_obj_tag(v_val_3434_) == 3)
{
lean_object* v_v_3435_; 
v_v_3435_ = lean_ctor_get(v_val_3434_, 0);
lean_inc(v_v_3435_);
lean_dec_ref(v_val_3434_);
return v_v_3435_;
}
else
{
lean_dec(v_val_3434_);
lean_inc(v_defValue_3431_);
return v_defValue_3431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__6___boxed(lean_object* v_opts_3436_, lean_object* v_opt_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__6(v_opts_3436_, v_opt_3437_);
lean_dec_ref(v_opt_3437_);
lean_dec_ref(v_opts_3436_);
return v_res_3438_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0));
v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
return v___x_3441_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3442_; double v___x_3443_; 
v___x_3442_ = lean_unsigned_to_nat(0u);
v___x_3443_ = lean_float_of_nat(v___x_3442_);
return v___x_3443_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3));
v___x_3446_ = l_Lean_stringToMessageData(v___x_3445_);
return v___x_3446_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5(void){
_start:
{
lean_object* v___x_3447_; double v___x_3448_; 
v___x_3447_ = lean_unsigned_to_nat(1000u);
v___x_3448_ = lean_float_of_nat(v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(lean_object* v_cls_3449_, uint8_t v_collapsed_3450_, lean_object* v_tag_3451_, lean_object* v_opts_3452_, uint8_t v_clsEnabled_3453_, lean_object* v_oldTraces_3454_, lean_object* v_msg_3455_, lean_object* v_resStartStop_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3566_; 
v_fst_3467_ = lean_ctor_get(v_resStartStop_3456_, 0);
v_snd_3468_ = lean_ctor_get(v_resStartStop_3456_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_resStartStop_3456_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3470_ = v_resStartStop_3456_;
v_isShared_3471_ = v_isSharedCheck_3566_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snd_3468_);
lean_inc(v_fst_3467_);
lean_dec(v_resStartStop_3456_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3566_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v_data_3475_; lean_object* v_fst_3486_; lean_object* v_snd_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3565_; 
v_fst_3486_ = lean_ctor_get(v_snd_3468_, 0);
v_snd_3487_ = lean_ctor_get(v_snd_3468_, 1);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_snd_3468_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3489_ = v_snd_3468_;
v_isShared_3490_ = v_isSharedCheck_3565_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_snd_3487_);
lean_inc(v_fst_3486_);
lean_dec(v_snd_3468_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3565_;
goto v_resetjp_3488_;
}
v___jp_3472_:
{
lean_object* v___x_3476_; 
v___x_3476_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___redArg(v_oldTraces_3454_, v_data_3475_, v___y_3473_, v___y_3474_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v___x_3477_; 
lean_dec_ref(v___x_3476_);
v___x_3477_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg(v_fst_3467_);
return v___x_3477_;
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec(v_fst_3467_);
v_a_3478_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3476_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3476_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; uint8_t v___x_3492_; lean_object* v___y_3494_; lean_object* v_a_3495_; uint8_t v___y_3519_; double v___y_3550_; 
v___x_3491_ = l_Lean_trace_profiler;
v___x_3492_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_opts_3452_, v___x_3491_);
if (v___x_3492_ == 0)
{
v___y_3519_ = v___x_3492_;
goto v___jp_3518_;
}
else
{
lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3555_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3556_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_opts_3452_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; double v___x_3559_; double v___x_3560_; double v___x_3561_; 
v___x_3557_ = l_Lean_trace_profiler_threshold;
v___x_3558_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__6(v_opts_3452_, v___x_3557_);
v___x_3559_ = lean_float_of_nat(v___x_3558_);
v___x_3560_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5);
v___x_3561_ = lean_float_div(v___x_3559_, v___x_3560_);
v___y_3550_ = v___x_3561_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; double v___x_3564_; 
v___x_3562_ = l_Lean_trace_profiler_threshold;
v___x_3563_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__6(v_opts_3452_, v___x_3562_);
v___x_3564_ = lean_float_of_nat(v___x_3563_);
v___y_3550_ = v___x_3564_;
goto v___jp_3549_;
}
}
v___jp_3493_:
{
uint8_t v_result_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v_result_3496_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__3(v_fst_3467_);
v___x_3497_ = l_Lean_TraceResult_toEmoji(v_result_3496_);
v___x_3498_ = l_Lean_stringToMessageData(v___x_3497_);
v___x_3499_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1);
if (v_isShared_3490_ == 0)
{
lean_ctor_set_tag(v___x_3489_, 7);
lean_ctor_set(v___x_3489_, 1, v___x_3499_);
lean_ctor_set(v___x_3489_, 0, v___x_3498_);
v___x_3501_ = v___x_3489_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v_m_3503_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set_tag(v___x_3470_, 7);
lean_ctor_set(v___x_3470_, 1, v_a_3495_);
lean_ctor_set(v___x_3470_, 0, v___x_3501_);
v_m_3503_ = v___x_3470_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_a_3495_);
v_m_3503_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; double v___x_3506_; lean_object* v_data_3507_; 
v___x_3504_ = lean_box(v_result_3496_);
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
v___x_3506_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2);
lean_inc_ref(v_tag_3451_);
lean_inc_ref(v___x_3505_);
lean_inc(v_cls_3449_);
v_data_3507_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3507_, 0, v_cls_3449_);
lean_ctor_set(v_data_3507_, 1, v___x_3505_);
lean_ctor_set(v_data_3507_, 2, v_tag_3451_);
lean_ctor_set_float(v_data_3507_, sizeof(void*)*3, v___x_3506_);
lean_ctor_set_float(v_data_3507_, sizeof(void*)*3 + 8, v___x_3506_);
lean_ctor_set_uint8(v_data_3507_, sizeof(void*)*3 + 16, v_collapsed_3450_);
if (v___x_3492_ == 0)
{
lean_dec_ref(v___x_3505_);
lean_dec(v_snd_3487_);
lean_dec(v_fst_3486_);
lean_dec_ref(v_tag_3451_);
lean_dec(v_cls_3449_);
v___y_3473_ = v___y_3494_;
v___y_3474_ = v_m_3503_;
v_data_3475_ = v_data_3507_;
goto v___jp_3472_;
}
else
{
lean_object* v_data_3508_; double v___x_3509_; double v___x_3510_; 
lean_dec_ref(v_data_3507_);
v_data_3508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3508_, 0, v_cls_3449_);
lean_ctor_set(v_data_3508_, 1, v___x_3505_);
lean_ctor_set(v_data_3508_, 2, v_tag_3451_);
v___x_3509_ = lean_unbox_float(v_fst_3486_);
lean_dec(v_fst_3486_);
lean_ctor_set_float(v_data_3508_, sizeof(void*)*3, v___x_3509_);
v___x_3510_ = lean_unbox_float(v_snd_3487_);
lean_dec(v_snd_3487_);
lean_ctor_set_float(v_data_3508_, sizeof(void*)*3 + 8, v___x_3510_);
lean_ctor_set_uint8(v_data_3508_, sizeof(void*)*3 + 16, v_collapsed_3450_);
v___y_3473_ = v___y_3494_;
v___y_3474_ = v_m_3503_;
v_data_3475_ = v_data_3508_;
goto v___jp_3472_;
}
}
}
}
v___jp_3513_:
{
lean_object* v_ref_3514_; lean_object* v___x_3515_; 
v_ref_3514_ = lean_ctor_get(v___y_3464_, 5);
lean_inc(v___y_3465_);
lean_inc_ref(v___y_3464_);
lean_inc(v___y_3463_);
lean_inc_ref(v___y_3462_);
lean_inc(v_fst_3467_);
v___x_3515_ = lean_apply_11(v_msg_3455_, v_fst_3467_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, lean_box(0));
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref(v___x_3515_);
lean_inc(v_ref_3514_);
v___y_3494_ = v_ref_3514_;
v_a_3495_ = v_a_3516_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3517_; 
lean_dec_ref(v___x_3515_);
v___x_3517_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4);
lean_inc(v_ref_3514_);
v___y_3494_ = v_ref_3514_;
v_a_3495_ = v___x_3517_;
goto v___jp_3493_;
}
}
v___jp_3518_:
{
if (v_clsEnabled_3453_ == 0)
{
if (v___y_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v_traceState_3521_; lean_object* v_env_3522_; lean_object* v_nextMacroScope_3523_; lean_object* v_ngen_3524_; lean_object* v_auxDeclNGen_3525_; lean_object* v_cache_3526_; lean_object* v_messages_3527_; lean_object* v_infoState_3528_; lean_object* v_snapshotTasks_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3548_; 
lean_del_object(v___x_3489_);
lean_dec(v_snd_3487_);
lean_dec(v_fst_3486_);
lean_del_object(v___x_3470_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v_msg_3455_);
lean_dec_ref(v_tag_3451_);
lean_dec(v_cls_3449_);
v___x_3520_ = lean_st_ref_take(v___y_3465_);
v_traceState_3521_ = lean_ctor_get(v___x_3520_, 4);
v_env_3522_ = lean_ctor_get(v___x_3520_, 0);
v_nextMacroScope_3523_ = lean_ctor_get(v___x_3520_, 1);
v_ngen_3524_ = lean_ctor_get(v___x_3520_, 2);
v_auxDeclNGen_3525_ = lean_ctor_get(v___x_3520_, 3);
v_cache_3526_ = lean_ctor_get(v___x_3520_, 5);
v_messages_3527_ = lean_ctor_get(v___x_3520_, 6);
v_infoState_3528_ = lean_ctor_get(v___x_3520_, 7);
v_snapshotTasks_3529_ = lean_ctor_get(v___x_3520_, 8);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3531_ = v___x_3520_;
v_isShared_3532_ = v_isSharedCheck_3548_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_snapshotTasks_3529_);
lean_inc(v_infoState_3528_);
lean_inc(v_messages_3527_);
lean_inc(v_cache_3526_);
lean_inc(v_traceState_3521_);
lean_inc(v_auxDeclNGen_3525_);
lean_inc(v_ngen_3524_);
lean_inc(v_nextMacroScope_3523_);
lean_inc(v_env_3522_);
lean_dec(v___x_3520_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3548_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
uint64_t v_tid_3533_; lean_object* v_traces_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3547_; 
v_tid_3533_ = lean_ctor_get_uint64(v_traceState_3521_, sizeof(void*)*1);
v_traces_3534_ = lean_ctor_get(v_traceState_3521_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_traceState_3521_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3536_ = v_traceState_3521_;
v_isShared_3537_ = v_isSharedCheck_3547_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_traces_3534_);
lean_dec(v_traceState_3521_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3547_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3538_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3454_, v_traces_3534_);
lean_dec_ref(v_traces_3534_);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3538_);
v___x_3540_ = v___x_3536_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3538_);
lean_ctor_set_uint64(v_reuseFailAlloc_3546_, sizeof(void*)*1, v_tid_3533_);
v___x_3540_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3542_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 4, v___x_3540_);
v___x_3542_ = v___x_3531_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_env_3522_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_nextMacroScope_3523_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_ngen_3524_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v_auxDeclNGen_3525_);
lean_ctor_set(v_reuseFailAlloc_3545_, 4, v___x_3540_);
lean_ctor_set(v_reuseFailAlloc_3545_, 5, v_cache_3526_);
lean_ctor_set(v_reuseFailAlloc_3545_, 6, v_messages_3527_);
lean_ctor_set(v_reuseFailAlloc_3545_, 7, v_infoState_3528_);
lean_ctor_set(v_reuseFailAlloc_3545_, 8, v_snapshotTasks_3529_);
v___x_3542_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = lean_st_ref_set(v___y_3465_, v___x_3542_);
lean_dec(v___y_3465_);
v___x_3544_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg(v_fst_3467_);
return v___x_3544_;
}
}
}
}
}
else
{
goto v___jp_3513_;
}
}
else
{
goto v___jp_3513_;
}
}
v___jp_3549_:
{
double v___x_3551_; double v___x_3552_; double v___x_3553_; uint8_t v___x_3554_; 
v___x_3551_ = lean_unbox_float(v_snd_3487_);
v___x_3552_ = lean_unbox_float(v_fst_3486_);
v___x_3553_ = lean_float_sub(v___x_3551_, v___x_3552_);
v___x_3554_ = lean_float_decLt(v___y_3550_, v___x_3553_);
v___y_3519_ = v___x_3554_;
goto v___jp_3518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(lean_object** _args){
lean_object* v_cls_3567_ = _args[0];
lean_object* v_collapsed_3568_ = _args[1];
lean_object* v_tag_3569_ = _args[2];
lean_object* v_opts_3570_ = _args[3];
lean_object* v_clsEnabled_3571_ = _args[4];
lean_object* v_oldTraces_3572_ = _args[5];
lean_object* v_msg_3573_ = _args[6];
lean_object* v_resStartStop_3574_ = _args[7];
lean_object* v___y_3575_ = _args[8];
lean_object* v___y_3576_ = _args[9];
lean_object* v___y_3577_ = _args[10];
lean_object* v___y_3578_ = _args[11];
lean_object* v___y_3579_ = _args[12];
lean_object* v___y_3580_ = _args[13];
lean_object* v___y_3581_ = _args[14];
lean_object* v___y_3582_ = _args[15];
lean_object* v___y_3583_ = _args[16];
lean_object* v___y_3584_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3585_; uint8_t v_clsEnabled_boxed_3586_; lean_object* v_res_3587_; 
v_collapsed_boxed_3585_ = lean_unbox(v_collapsed_3568_);
v_clsEnabled_boxed_3586_ = lean_unbox(v_clsEnabled_3571_);
v_res_3587_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_cls_3567_, v_collapsed_boxed_3585_, v_tag_3569_, v_opts_3570_, v_clsEnabled_boxed_3586_, v_oldTraces_3572_, v_msg_3573_, v_resStartStop_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec_ref(v_opts_3570_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0(uint8_t v___x_3588_, lean_object* v_e_3589_, lean_object* v_snd_3590_, lean_object* v_proc_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
if (v___x_3588_ == 0)
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_3589_, v_snd_3590_, v_proc_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3602_;
}
else
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_apply_11(v_proc_3591_, v_e_3589_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, lean_box(0));
return v___x_3603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0___boxed(lean_object* v___x_3604_, lean_object* v_e_3605_, lean_object* v_snd_3606_, lean_object* v_proc_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
uint8_t v___x_48774__boxed_3618_; lean_object* v_res_3619_; 
v___x_48774__boxed_3618_ = lean_unbox(v___x_3604_);
v_res_3619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0(v___x_48774__boxed_3618_, v_e_3605_, v_snd_3606_, v_proc_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v_snd_3606_);
return v_res_3619_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__0));
v___x_3622_ = l_Lean_stringToMessageData(v___x_3621_);
return v___x_3622_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__2));
v___x_3625_ = l_Lean_stringToMessageData(v___x_3624_);
return v___x_3625_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__4));
v___x_3628_ = l_Lean_stringToMessageData(v___x_3627_);
return v___x_3628_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__6));
v___x_3631_ = l_Lean_stringToMessageData(v___x_3630_);
return v___x_3631_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__9(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__8));
v___x_3634_ = l_Lean_stringToMessageData(v___x_3633_);
return v___x_3634_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__11(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__10));
v___x_3637_ = l_Lean_stringToMessageData(v___x_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1(lean_object* v___x_3638_, lean_object* v_e_3639_, lean_object* v_x_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
if (lean_obj_tag(v_x_3640_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3665_; 
lean_dec_ref(v_e_3639_);
v_a_3651_ = lean_ctor_get(v_x_3640_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_x_3640_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3653_ = v_x_3640_;
v_isShared_3654_ = v_isSharedCheck_3665_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v_x_3640_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3665_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1);
v___x_3656_ = l_Lean_MessageData_ofName(v___x_3638_);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__3);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = l_Lean_Exception_toMessageData(v_a_3651_);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3661_);
v___x_3663_ = v___x_3653_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3704_; 
v_a_3666_ = lean_ctor_get(v_x_3640_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_x_3640_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3668_ = v_x_3640_;
v_isShared_3669_ = v_isSharedCheck_3704_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v_x_3640_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3704_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
if (lean_obj_tag(v_a_3666_) == 0)
{
uint8_t v_done_3670_; 
v_done_3670_ = lean_ctor_get_uint8(v_a_3666_, 0);
lean_dec_ref(v_a_3666_);
if (v_done_3670_ == 1)
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3671_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1);
v___x_3672_ = l_Lean_MessageData_ofName(v___x_3638_);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__5);
v___x_3675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3673_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = l_Lean_indentExpr(v_e_3639_);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3677_);
v___x_3679_ = v___x_3668_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
else
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_dec_ref(v_e_3639_);
v___x_3681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1);
v___x_3682_ = l_Lean_MessageData_ofName(v___x_3638_);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__7);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3685_);
v___x_3687_ = v___x_3668_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
else
{
lean_object* v_e_x27_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v_e_x27_3689_ = lean_ctor_get(v_a_3666_, 0);
lean_inc_ref(v_e_x27_3689_);
lean_dec_ref(v_a_3666_);
v___x_3690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__1);
v___x_3691_ = l_Lean_MessageData_ofName(v___x_3638_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__9);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = l_Lean_indentExpr(v_e_3639_);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___closed__11);
v___x_3698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = l_Lean_indentExpr(v_e_x27_3689_);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3700_);
v___x_3702_ = v___x_3668_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___boxed(lean_object* v___x_3705_, lean_object* v_e_3706_, lean_object* v_x_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1(v___x_3705_, v_e_3706_, v_x_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
return v_res_3718_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__7(void){
_start:
{
lean_object* v___x_3740_; double v___x_3741_; 
v___x_3740_ = lean_unsigned_to_nat(1000000000u);
v___x_3741_ = lean_float_of_nat(v___x_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4(lean_object* v_erased_3742_, lean_object* v_e_3743_, lean_object* v_as_3744_, size_t v_sz_3745_, size_t v_i_3746_, lean_object* v_b_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_a_3759_; uint8_t v___x_3763_; 
v___x_3763_ = lean_usize_dec_lt(v_i_3746_, v_sz_3745_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v_e_3743_);
lean_dec_ref(v_erased_3742_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_b_3747_);
return v___x_3764_;
}
else
{
lean_object* v_a_3765_; lean_object* v_fst_3766_; lean_object* v_toCbvSimprocOLeanEntry_3767_; lean_object* v_snd_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3918_; 
lean_dec_ref(v_b_3747_);
v_a_3765_ = lean_array_uget(v_as_3744_, v_i_3746_);
v_fst_3766_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_fst_3766_);
v_toCbvSimprocOLeanEntry_3767_ = lean_ctor_get(v_fst_3766_, 0);
lean_inc_ref(v_toCbvSimprocOLeanEntry_3767_);
v_snd_3768_ = lean_ctor_get(v_a_3765_, 1);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; 
v_unused_3919_ = lean_ctor_get(v_a_3765_, 0);
lean_dec(v_unused_3919_);
v___x_3770_ = v_a_3765_;
v_isShared_3771_ = v_isSharedCheck_3918_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_snd_3768_);
lean_dec(v_a_3765_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3918_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v_proc_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3916_; 
v_proc_3772_ = lean_ctor_get(v_fst_3766_, 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_fst_3766_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v_fst_3766_, 0);
lean_dec(v_unused_3917_);
v___x_3774_ = v_fst_3766_;
v_isShared_3775_ = v_isSharedCheck_3916_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_proc_3772_);
lean_dec(v_fst_3766_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3916_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v_declName_3776_; lean_object* v___x_3777_; lean_object* v___y_3779_; lean_object* v___x_3785_; uint8_t v___x_3786_; lean_object* v___y_3788_; 
v_declName_3776_ = lean_ctor_get(v_toCbvSimprocOLeanEntry_3767_, 0);
lean_inc(v_declName_3776_);
lean_dec_ref(v_toCbvSimprocOLeanEntry_3767_);
v___x_3777_ = lean_box(0);
v___x_3785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__0));
lean_inc_ref(v_erased_3742_);
v___x_3786_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_erased_3742_, v_declName_3776_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3810_; lean_object* v_options_3811_; uint8_t v_hasTrace_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__1));
v_options_3811_ = lean_ctor_get(v___y_3755_, 2);
v_hasTrace_3812_ = lean_ctor_get_uint8(v_options_3811_, sizeof(void*)*1);
v___x_3813_ = lean_unsigned_to_nat(0u);
v___x_3814_ = lean_nat_dec_eq(v_snd_3768_, v___x_3813_);
if (v_hasTrace_3812_ == 0)
{
lean_object* v___x_3815_; 
lean_dec(v_declName_3776_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc_ref(v_e_3743_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0(v___x_3814_, v_e_3743_, v_snd_3768_, v_proc_3772_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v_snd_3768_);
v___y_3788_ = v___x_3815_;
goto v___jp_3787_;
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__2));
v___x_3817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__5));
v___x_3818_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___x_3817_, v___y_3755_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___f_3824_; lean_object* v___x_3825_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v_a_3829_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v_a_3845_; uint8_t v___x_3904_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
v___x_3820_ = l_Lean_privateToUserName(v_declName_3776_);
v___x_3821_ = lean_box(0);
v___x_3822_ = l_Lean_Name_replacePrefix(v___x_3820_, v___x_3810_, v___x_3821_);
v___x_3823_ = l_Lean_Name_replacePrefix(v___x_3822_, v___x_3816_, v___x_3821_);
lean_inc_ref(v_e_3743_);
v___f_3824_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__1___boxed), 13, 2);
lean_closure_set(v___f_3824_, 0, v___x_3823_);
lean_closure_set(v___f_3824_, 1, v_e_3743_);
v___x_3825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__6));
v___x_3904_ = lean_unbox(v_a_3819_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; uint8_t v___x_3906_; 
v___x_3905_ = l_Lean_trace_profiler;
v___x_3906_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_options_3811_, v___x_3905_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; 
lean_dec_ref(v___f_3824_);
lean_dec(v_a_3819_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc_ref(v_e_3743_);
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0(v___x_3814_, v_e_3743_, v_snd_3768_, v_proc_3772_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v_snd_3768_);
v___y_3788_ = v___x_3907_;
goto v___jp_3787_;
}
else
{
goto v___jp_3855_;
}
}
else
{
goto v___jp_3855_;
}
v___jp_3826_:
{
lean_object* v___x_3830_; double v___x_3831_; double v___x_3832_; double v___x_3833_; double v___x_3834_; double v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; lean_object* v___x_3841_; 
v___x_3830_ = lean_io_mono_nanos_now();
v___x_3831_ = lean_float_of_nat(v___y_3827_);
v___x_3832_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__7);
v___x_3833_ = lean_float_div(v___x_3831_, v___x_3832_);
v___x_3834_ = lean_float_of_nat(v___x_3830_);
v___x_3835_ = lean_float_div(v___x_3834_, v___x_3832_);
v___x_3836_ = lean_box_float(v___x_3833_);
v___x_3837_ = lean_box_float(v___x_3835_);
v___x_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3836_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3839_, 0, v_a_3829_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___x_3840_ = lean_unbox(v_a_3819_);
lean_dec(v_a_3819_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
v___x_3841_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v___x_3817_, v_hasTrace_3812_, v___x_3825_, v_options_3811_, v___x_3840_, v___y_3828_, v___f_3824_, v___x_3839_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
v___y_3788_ = v___x_3841_;
goto v___jp_3787_;
}
v___jp_3842_:
{
lean_object* v___x_3846_; double v___x_3847_; double v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; uint8_t v___x_3853_; lean_object* v___x_3854_; 
v___x_3846_ = lean_io_get_num_heartbeats();
v___x_3847_ = lean_float_of_nat(v___y_3843_);
v___x_3848_ = lean_float_of_nat(v___x_3846_);
v___x_3849_ = lean_box_float(v___x_3847_);
v___x_3850_ = lean_box_float(v___x_3848_);
v___x_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v_a_3845_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_unbox(v_a_3819_);
lean_dec(v_a_3819_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
v___x_3854_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v___x_3817_, v_hasTrace_3812_, v___x_3825_, v_options_3811_, v___x_3853_, v___y_3844_, v___f_3824_, v___x_3852_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
v___y_3788_ = v___x_3854_;
goto v___jp_3787_;
}
v___jp_3855_:
{
lean_object* v___x_3856_; 
v___x_3856_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___redArg(v___y_3756_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3859_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_options_3811_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_io_mono_nanos_now();
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc_ref(v_e_3743_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0(v___x_3814_, v_e_3743_, v_snd_3768_, v_proc_3772_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v_snd_3768_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set_tag(v___x_3864_, 1);
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
v___y_3827_ = v___x_3860_;
v___y_3828_ = v_a_3857_;
v_a_3829_ = v___x_3867_;
goto v___jp_3826_;
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
v_a_3870_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3861_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3861_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
lean_ctor_set_tag(v___x_3872_, 0);
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
v___y_3827_ = v___x_3860_;
v___y_3828_ = v_a_3857_;
v_a_3829_ = v___x_3875_;
goto v___jp_3826_;
}
}
}
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_io_get_num_heartbeats();
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc_ref(v_e_3743_);
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___lam__0(v___x_3814_, v_e_3743_, v_snd_3768_, v_proc_3772_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v_snd_3768_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 1);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
v___y_3843_ = v___x_3878_;
v___y_3844_ = v_a_3857_;
v_a_3845_ = v___x_3885_;
goto v___jp_3842_;
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_a_3888_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3879_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3879_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set_tag(v___x_3890_, 0);
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
v___y_3843_ = v___x_3878_;
v___y_3844_ = v_a_3857_;
v_a_3845_ = v___x_3893_;
goto v___jp_3842_;
}
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec_ref(v___f_3824_);
lean_dec(v_a_3819_);
lean_del_object(v___x_3774_);
lean_dec_ref(v_proc_3772_);
lean_del_object(v___x_3770_);
lean_dec(v_snd_3768_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v_e_3743_);
lean_dec_ref(v_erased_3742_);
v_a_3896_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3856_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3856_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec(v_declName_3776_);
lean_del_object(v___x_3774_);
lean_dec_ref(v_proc_3772_);
lean_del_object(v___x_3770_);
lean_dec(v_snd_3768_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v_e_3743_);
lean_dec_ref(v_erased_3742_);
v_a_3908_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3818_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3818_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
else
{
lean_dec(v_declName_3776_);
lean_del_object(v___x_3774_);
lean_dec_ref(v_proc_3772_);
lean_del_object(v___x_3770_);
lean_dec(v_snd_3768_);
v_a_3759_ = v___x_3785_;
goto v___jp_3758_;
}
v___jp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___y_3779_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v___x_3777_);
lean_ctor_set(v___x_3770_, 0, v___x_3780_);
v___x_3782_ = v___x_3770_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3777_);
v___x_3782_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
return v___x_3783_;
}
}
v___jp_3787_:
{
if (lean_obj_tag(v___y_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3801_; 
v_a_3789_ = lean_ctor_get(v___y_3788_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___y_3788_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3791_ = v___y_3788_;
v_isShared_3792_ = v_isSharedCheck_3801_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___y_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3801_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
if (lean_obj_tag(v_a_3789_) == 1)
{
lean_del_object(v___x_3791_);
lean_del_object(v___x_3774_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v_e_3743_);
lean_dec_ref(v_erased_3742_);
v___y_3779_ = v_a_3789_;
goto v___jp_3778_;
}
else
{
if (v___x_3786_ == 0)
{
lean_del_object(v___x_3770_);
if (lean_obj_tag(v_a_3789_) == 0)
{
uint8_t v_done_3793_; 
v_done_3793_ = lean_ctor_get_uint8(v_a_3789_, 0);
if (v_done_3793_ == 1)
{
lean_object* v___x_3794_; lean_object* v___x_3796_; 
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v_e_3743_);
lean_dec_ref(v_erased_3742_);
v___x_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3794_, 0, v_a_3789_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 1, v___x_3777_);
lean_ctor_set(v___x_3774_, 0, v___x_3794_);
v___x_3796_ = v___x_3774_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3794_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3777_);
v___x_3796_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3798_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3796_);
v___x_3798_ = v___x_3791_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
else
{
lean_dec_ref(v_a_3789_);
lean_del_object(v___x_3791_);
lean_del_object(v___x_3774_);
v_a_3759_ = v___x_3785_;
goto v___jp_3758_;
}
}
else
{
lean_del_object(v___x_3791_);
lean_dec(v_a_3789_);
lean_del_object(v___x_3774_);
v_a_3759_ = v___x_3785_;
goto v___jp_3758_;
}
}
else
{
lean_del_object(v___x_3791_);
lean_del_object(v___x_3774_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v_e_3743_);
lean_dec_ref(v_erased_3742_);
v___y_3779_ = v_a_3789_;
goto v___jp_3778_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_del_object(v___x_3774_);
lean_del_object(v___x_3770_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v_e_3743_);
lean_dec_ref(v_erased_3742_);
v_a_3802_ = lean_ctor_get(v___y_3788_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___y_3788_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___y_3788_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___y_3788_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
}
v___jp_3758_:
{
size_t v___x_3760_; size_t v___x_3761_; 
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_add(v_i_3746_, v___x_3760_);
v_i_3746_ = v___x_3761_;
v_b_3747_ = v_a_3759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___boxed(lean_object* v_erased_3920_, lean_object* v_e_3921_, lean_object* v_as_3922_, lean_object* v_sz_3923_, lean_object* v_i_3924_, lean_object* v_b_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
size_t v_sz_boxed_3936_; size_t v_i_boxed_3937_; lean_object* v_res_3938_; 
v_sz_boxed_3936_ = lean_unbox_usize(v_sz_3923_);
lean_dec(v_sz_3923_);
v_i_boxed_3937_ = lean_unbox_usize(v_i_3924_);
lean_dec(v_i_3924_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4(v_erased_3920_, v_e_3921_, v_as_3922_, v_sz_boxed_3936_, v_i_boxed_3937_, v_b_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec_ref(v_as_3922_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object* v_tree_3941_, lean_object* v_erased_3942_, lean_object* v_e_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v_candidates_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v_candidates_3954_ = l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_tree_3941_, v_e_3943_);
v___x_3955_ = lean_array_get_size(v_candidates_3954_);
v___x_3956_ = lean_unsigned_to_nat(0u);
v___x_3957_ = lean_nat_dec_eq(v___x_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; size_t v_sz_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
v___x_3958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4___closed__0));
v_sz_3959_ = lean_array_size(v_candidates_3954_);
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__4(v_erased_3942_, v_e_3943_, v_candidates_3954_, v_sz_3959_, v___x_3960_, v___x_3958_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
lean_dec_ref(v_candidates_3954_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3975_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3975_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3975_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v_fst_3966_; 
v_fst_3966_ = lean_ctor_get(v_a_3962_, 0);
lean_inc(v_fst_3966_);
lean_dec(v_a_3962_);
if (lean_obj_tag(v_fst_3966_) == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_3967_, 0, v___x_3957_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3967_);
v___x_3969_ = v___x_3964_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
else
{
lean_object* v_val_3971_; lean_object* v___x_3973_; 
v_val_3971_ = lean_ctor_get(v_fst_3966_, 0);
lean_inc(v_val_3971_);
lean_dec_ref(v_fst_3966_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v_val_3971_);
v___x_3973_ = v___x_3964_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_val_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
v_a_3976_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3961_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3961_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
else
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_dec_ref(v_candidates_3954_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
lean_dec(v_a_3948_);
lean_dec_ref(v_a_3947_);
lean_dec(v_a_3946_);
lean_dec_ref(v_a_3945_);
lean_dec(v_a_3944_);
lean_dec_ref(v_e_3943_);
lean_dec_ref(v_erased_3942_);
v___x_3984_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0));
v___x_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
return v___x_3985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(lean_object* v_tree_3986_, lean_object* v_erased_3987_, lean_object* v_e_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_tree_3986_, v_erased_3987_, v_e_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5(lean_object* v_00_u03b1_4000_, lean_object* v_x_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___redArg(v_x_4001_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4013_, lean_object* v_x_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__5(v_00_u03b1_4013_, v_x_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4(lean_object* v_oldTraces_4026_, lean_object* v_data_4027_, lean_object* v_ref_4028_, lean_object* v_msg_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___redArg(v_oldTraces_4026_, v_data_4027_, v_ref_4028_, v_msg_4029_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4___boxed(lean_object* v_oldTraces_4041_, lean_object* v_data_4042_, lean_object* v_ref_4043_, lean_object* v_msg_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3_spec__4(v_oldTraces_4041_, v_data_4042_, v_ref_4043_, v_msg_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v___y_4053_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
return v_res_4055_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Pattern(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef);
lean_dec_ref(res);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default);
l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState = _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState();
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState);
res = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt);
lean_dec_ref(res);
res = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef);
lean_dec_ref(res);
res = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
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
