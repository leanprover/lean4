// Lean compiler output
// Module: Lean.Linter.Extra.UnusedDecidableInType
// Imports: public import Lean.Linter.Basic public import Lean.Meta.ForEachExpr public import Lean.Meta.Sorry public import Lean.PrivateName public import Lean.Server.InfoUtils public import Lean.Linter.Util
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Linter_getDeclsByBody(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unusedDecidableInType"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(126, 106, 196, 225, 81, 30, 137, 135)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 221, .m_capacity = 221, .m_length = 220, .m_data = "enable the unused `Decidable*` instance linter, which lints against `Decidable*` instances in the hypotheses of theorems which are not used in the type, and can therefore be replaced by a use of `classical` in the proof."};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Extra"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(98, 33, 172, 180, 73, 123, 191, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(105, 61, 181, 137, 182, 231, 65, 137)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(102, 30, 130, 216, 127, 103, 0, 158)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = " (used in type, but only in a proof)"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "] (#"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "parameter #"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0(lean_object*);
static const lean_closure_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "\n  • "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " in its type"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " outside of proofs"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` does not use the following "};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8_value;
static lean_once_cell_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hypotheses"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hypothesis"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "DecidableRel"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 165, 128, 103, 195, 117, 187, 51)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "DecidableEq"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 163, 7, 138, 119, 67, 2, 253)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "DecidableLE"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(33, 198, 120, 234, 95, 60, 229, 135)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "DecidableLT"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(113, 2, 59, 91, 108, 226, 67, 238)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DecidablePred"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(16, 236, 239, 206, 255, 167, 201, 157)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0 = (const lean_object*)&l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "\n\nConsider removing "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 141, .m_capacity = 141, .m_length = 140, .m_data = " and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level)."};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "these hypotheses"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "this hypothesis"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0 = (const lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1 = (const lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "UnusedDecidableInType"};
static const lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2 = (const lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2_value;
static const lean_string_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unusedDecidableInTypeLinter"};
static const lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3 = (const lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 148, 165, 15, 81, 68, 12, 199)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(221, 46, 57, 107, 248, 119, 253, 192)}};
static const lean_ctor_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_3),((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 159, 172, 174, 52, 152, 126, 114)}};
static const lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4 = (const lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value;
static const lean_ctor_object l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1_value),((lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value)}};
static const lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5 = (const lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter = (const lean_object*)&l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(lean_object* v_p_1_, lean_object* v_type_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Lean_Expr_cleanupAnnotations(v_type_2_);
v___x_4_ = l_Lean_Expr_getAppFn_x27(v___x_3_);
lean_dec_ref(v___x_3_);
switch(lean_obj_tag(v___x_4_))
{
case 4:
{
lean_object* v_declName_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_declName_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_declName_5_);
lean_dec_ref_known(v___x_4_, 2);
v___x_6_ = lean_apply_1(v_p_1_, v_declName_5_);
v___x_7_ = lean_unbox(v___x_6_);
return v___x_7_;
}
case 7:
{
lean_object* v_body_8_; 
v_body_8_ = lean_ctor_get(v___x_4_, 2);
lean_inc_ref(v_body_8_);
lean_dec_ref_known(v___x_4_, 3);
v_type_2_ = v_body_8_;
goto _start;
}
default: 
{
uint8_t v___x_10_; 
lean_dec_ref(v___x_4_);
lean_dec_ref(v_p_1_);
v___x_10_ = 0;
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP___boxed(lean_object* v_p_11_, lean_object* v_type_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(v_p_11_, v_type_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(lean_object* v_p_15_, lean_object* v_e_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Expr_cleanupAnnotations(v_e_16_);
switch(lean_obj_tag(v___x_17_))
{
case 7:
{
lean_object* v_binderType_18_; lean_object* v_body_19_; uint8_t v_binderInfo_20_; uint8_t v___y_22_; uint8_t v___x_24_; 
v_binderType_18_ = lean_ctor_get(v___x_17_, 1);
lean_inc_ref(v_binderType_18_);
v_body_19_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_body_19_);
v_binderInfo_20_ = lean_ctor_get_uint8(v___x_17_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_17_, 3);
v___x_24_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_20_);
if (v___x_24_ == 0)
{
lean_dec_ref(v_binderType_18_);
v___y_22_ = v___x_24_;
goto v___jp_21_;
}
else
{
lean_object* v___x_25_; uint8_t v___x_26_; 
lean_inc_ref(v_p_15_);
v___x_25_ = lean_apply_1(v_p_15_, v_binderType_18_);
v___x_26_ = lean_unbox(v___x_25_);
v___y_22_ = v___x_26_;
goto v___jp_21_;
}
v___jp_21_:
{
if (v___y_22_ == 0)
{
v_e_16_ = v_body_19_;
goto _start;
}
else
{
lean_dec_ref(v_body_19_);
lean_dec_ref(v_p_15_);
return v___y_22_;
}
}
}
case 8:
{
lean_object* v_body_27_; 
v_body_27_ = lean_ctor_get(v___x_17_, 3);
lean_inc_ref(v_body_27_);
lean_dec_ref_known(v___x_17_, 4);
v_e_16_ = v_body_27_;
goto _start;
}
default: 
{
uint8_t v___x_29_; 
lean_dec_ref(v___x_17_);
lean_dec_ref(v_p_15_);
v___x_29_ = 0;
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf___boxed(lean_object* v_p_30_, lean_object* v_e_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(v_p_30_, v_e_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(lean_object* v_p_34_, lean_object* v_body_35_, lean_object* v_current_36_, lean_object* v_acc_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Expr_cleanupAnnotations(v_body_35_);
switch(lean_obj_tag(v___x_38_))
{
case 7:
{
lean_object* v_binderType_39_; lean_object* v_body_40_; uint8_t v_binderInfo_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___y_45_; uint8_t v___x_52_; 
v_binderType_39_ = lean_ctor_get(v___x_38_, 1);
lean_inc_ref(v_binderType_39_);
v_body_40_ = lean_ctor_get(v___x_38_, 2);
lean_inc_ref(v_body_40_);
v_binderInfo_41_ = lean_ctor_get_uint8(v___x_38_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_38_, 3);
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_current_36_, v___x_42_);
v___x_52_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_41_);
if (v___x_52_ == 0)
{
lean_dec_ref(v_binderType_39_);
v___y_45_ = v___x_52_;
goto v___jp_44_;
}
else
{
lean_object* v___x_53_; uint8_t v___x_54_; 
lean_inc_ref(v_p_34_);
v___x_53_ = lean_apply_1(v_p_34_, v_binderType_39_);
v___x_54_ = lean_unbox(v___x_53_);
v___y_45_ = v___x_54_;
goto v___jp_44_;
}
v___jp_44_:
{
if (v___y_45_ == 0)
{
lean_dec(v_current_36_);
v_body_35_ = v_body_40_;
v_current_36_ = v___x_43_;
goto _start;
}
else
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_expr_has_loose_bvar(v_body_40_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; 
v___x_49_ = lean_array_push(v_acc_37_, v_current_36_);
v_body_35_ = v_body_40_;
v_current_36_ = v___x_43_;
v_acc_37_ = v___x_49_;
goto _start;
}
else
{
lean_dec(v_current_36_);
v_body_35_ = v_body_40_;
v_current_36_ = v___x_43_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_body_55_; 
v_body_55_ = lean_ctor_get(v___x_38_, 3);
lean_inc_ref(v_body_55_);
lean_dec_ref_known(v___x_38_, 4);
v_body_35_ = v_body_55_;
goto _start;
}
default: 
{
lean_dec_ref(v___x_38_);
lean_dec(v_current_36_);
lean_dec_ref(v_p_34_);
return v_acc_37_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(lean_object* v_p_59_, lean_object* v_e_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0));
v___x_63_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(v_p_59_, v_e_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(lean_object* v_env_64_, lean_object* v_p_65_, lean_object* v_decl_66_, uint8_t v_skipRealize_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Environment_findAsync_x3f(v_env_64_, v_decl_66_, v_skipRealize_67_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v___x_69_; 
lean_dec_ref(v_p_65_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_83_; 
v_val_70_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_83_ == 0)
{
v___x_72_ = v___x_68_;
v_isShared_73_ = v_isSharedCheck_83_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_val_70_);
lean_dec(v___x_68_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_83_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
uint8_t v_kind_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_kind_74_ = lean_ctor_get_uint8(v_val_70_, sizeof(void*)*3);
v___x_75_ = lean_box(v_kind_74_);
v___x_76_ = lean_apply_1(v_p_65_, v___x_75_);
v___x_77_ = lean_unbox(v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; 
lean_del_object(v___x_72_);
lean_dec(v_val_70_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = l_Lean_AsyncConstantInfo_toConstantVal(v_val_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_79_);
v___x_81_ = v___x_72_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f___boxed(lean_object* v_env_84_, lean_object* v_p_85_, lean_object* v_decl_86_, lean_object* v_skipRealize_87_){
_start:
{
uint8_t v_skipRealize_boxed_88_; lean_object* v_res_89_; 
v_skipRealize_boxed_88_ = lean_unbox(v_skipRealize_87_);
v_res_89_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_84_, v_p_85_, v_decl_86_, v_skipRealize_boxed_88_);
return v_res_89_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(uint8_t v_x_90_){
_start:
{
if (v_x_90_ == 1)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0___boxed(lean_object* v_x_93_){
_start:
{
uint8_t v_x_22__boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_x_22__boxed_94_ = lean_unbox(v_x_93_);
v_res_95_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(v_x_22__boxed_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(lean_object* v_env_98_, lean_object* v_decl_99_, uint8_t v_skipRealize_100_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_101_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0));
v___x_102_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_98_, v___f_101_, v_decl_99_, v_skipRealize_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___boxed(lean_object* v_env_103_, lean_object* v_decl_104_, lean_object* v_skipRealize_105_){
_start:
{
uint8_t v_skipRealize_boxed_106_; lean_object* v_res_107_; 
v_skipRealize_boxed_106_ = lean_unbox(v_skipRealize_105_);
v_res_107_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_103_, v_decl_104_, v_skipRealize_boxed_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(lean_object* v_name_108_, lean_object* v_decl_109_, lean_object* v_ref_110_){
_start:
{
lean_object* v_defValue_112_; lean_object* v_descr_113_; lean_object* v_deprecation_x3f_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_defValue_112_ = lean_ctor_get(v_decl_109_, 0);
v_descr_113_ = lean_ctor_get(v_decl_109_, 1);
v_deprecation_x3f_114_ = lean_ctor_get(v_decl_109_, 2);
v___x_115_ = lean_alloc_ctor(1, 0, 1);
v___x_116_ = lean_unbox(v_defValue_112_);
lean_ctor_set_uint8(v___x_115_, 0, v___x_116_);
lean_inc(v_deprecation_x3f_114_);
lean_inc_ref(v_descr_113_);
lean_inc_n(v_name_108_, 2);
v___x_117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_117_, 0, v_name_108_);
lean_ctor_set(v___x_117_, 1, v_ref_110_);
lean_ctor_set(v___x_117_, 2, v___x_115_);
lean_ctor_set(v___x_117_, 3, v_descr_113_);
lean_ctor_set(v___x_117_, 4, v_deprecation_x3f_114_);
v___x_118_ = lean_register_option(v_name_108_, v___x_117_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v___x_118_, 0);
lean_dec(v_unused_127_);
v___x_120_ = v___x_118_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_dec(v___x_118_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
lean_inc(v_defValue_112_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_name_108_);
lean_ctor_set(v___x_122_, 1, v_defValue_112_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_dec(v_name_108_);
v_a_128_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_118_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_118_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_136_, lean_object* v_decl_137_, lean_object* v_ref_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v_name_136_, v_decl_137_, v_ref_138_);
lean_dec_ref(v_decl_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_166_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_167_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_168_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4____boxed(lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
return v_res_170_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6));
v___x_182_ = l_Lean_stringToMessageData(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0(lean_object* v_param_186_){
_start:
{
lean_object* v_type_x3f_187_; lean_object* v_idx_188_; uint8_t v_appearsInTypeProof_189_; lean_object* v___y_191_; 
v_type_x3f_187_ = lean_ctor_get(v_param_186_, 1);
lean_inc(v_type_x3f_187_);
v_idx_188_ = lean_ctor_get(v_param_186_, 2);
lean_inc(v_idx_188_);
v_appearsInTypeProof_189_ = lean_ctor_get_uint8(v_param_186_, sizeof(void*)*3);
lean_dec_ref(v_param_186_);
if (lean_obj_tag(v_type_x3f_187_) == 1)
{
lean_object* v_val_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_213_; 
v_val_194_ = lean_ctor_get(v_type_x3f_187_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_type_x3f_187_);
if (v_isSharedCheck_213_ == 0)
{
v___x_196_ = v_type_x3f_187_;
v_isShared_197_ = v_isSharedCheck_213_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_val_194_);
lean_dec(v_type_x3f_187_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_213_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_198_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
v___x_199_ = l_Lean_MessageData_ofExpr(v_val_194_);
v___x_200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
v___x_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_idx_188_, v___x_203_);
lean_dec(v_idx_188_);
v___x_205_ = l_Nat_reprFast(v___x_204_);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 3);
lean_ctor_set(v___x_196_, 0, v___x_205_);
v___x_207_ = v___x_196_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_212_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_208_ = l_Lean_MessageData_ofFormat(v___x_207_);
v___x_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_202_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
v___x_211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___y_191_ = v___x_211_;
goto v___jp_190_;
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_type_x3f_187_);
v___x_214_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_idx_188_, v___x_215_);
lean_dec(v_idx_188_);
v___x_217_ = l_Nat_reprFast(v___x_216_);
v___x_218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
v___x_219_ = l_Lean_MessageData_ofFormat(v___x_218_);
v___x_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_214_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___y_191_ = v___x_220_;
goto v___jp_190_;
}
v___jp_190_:
{
if (v_appearsInTypeProof_189_ == 0)
{
return v___y_191_;
}
else
{
lean_object* v___x_192_; lean_object* v_msg_193_; 
v___x_192_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
v_msg_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_193_, 0, v___y_191_);
lean_ctor_set(v_msg_193_, 1, v___x_192_);
return v_msg_193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(lean_object* v_as_223_, size_t v_i_224_, size_t v_stop_225_, lean_object* v_b_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_eq(v_i_224_, v_stop_225_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; size_t v___x_230_; size_t v___x_231_; 
v___x_228_ = lean_array_uget_borrowed(v_as_223_, v_i_224_);
lean_inc(v___x_228_);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v_b_226_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_224_, v___x_230_);
v_i_224_ = v___x_231_;
v_b_226_ = v___x_229_;
goto _start;
}
else
{
return v_b_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2___boxed(lean_object* v_as_233_, lean_object* v_i_234_, lean_object* v_stop_235_, lean_object* v_b_236_){
_start:
{
size_t v_i_boxed_237_; size_t v_stop_boxed_238_; lean_object* v_res_239_; 
v_i_boxed_237_ = lean_unbox_usize(v_i_234_);
lean_dec(v_i_234_);
v_stop_boxed_238_ = lean_unbox_usize(v_stop_235_);
lean_dec(v_stop_235_);
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v_as_233_, v_i_boxed_237_, v_stop_boxed_238_, v_b_236_);
lean_dec_ref(v_as_233_);
return v_res_239_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(lean_object* v_as_240_, size_t v_i_241_, size_t v_stop_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = lean_usize_dec_eq(v_i_241_, v_stop_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint8_t v_appearsInTypeProof_245_; 
v___x_244_ = lean_array_uget_borrowed(v_as_240_, v_i_241_);
v_appearsInTypeProof_245_ = lean_ctor_get_uint8(v___x_244_, sizeof(void*)*3);
if (v_appearsInTypeProof_245_ == 0)
{
size_t v___x_246_; size_t v___x_247_; 
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_add(v_i_241_, v___x_246_);
v_i_241_ = v___x_247_;
goto _start;
}
else
{
return v_appearsInTypeProof_245_;
}
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3___boxed(lean_object* v_as_250_, lean_object* v_i_251_, lean_object* v_stop_252_){
_start:
{
size_t v_i_boxed_253_; size_t v_stop_boxed_254_; uint8_t v_res_255_; lean_object* v_r_256_; 
v_i_boxed_253_ = lean_unbox_usize(v_i_251_);
lean_dec(v_i_251_);
v_stop_boxed_254_ = lean_unbox_usize(v_stop_252_);
lean_dec(v_stop_252_);
v_res_255_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_as_250_, v_i_boxed_253_, v_stop_boxed_254_);
lean_dec_ref(v_as_250_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(size_t v_sz_257_, size_t v_i_258_, lean_object* v_bs_259_){
_start:
{
uint8_t v___x_260_; 
v___x_260_ = lean_usize_dec_lt(v_i_258_, v_sz_257_);
if (v___x_260_ == 0)
{
return v_bs_259_;
}
else
{
lean_object* v_v_261_; lean_object* v_type_x3f_262_; lean_object* v_idx_263_; lean_object* v___x_264_; lean_object* v_bs_x27_265_; lean_object* v___y_267_; lean_object* v___y_273_; 
v_v_261_ = lean_array_uget(v_bs_259_, v_i_258_);
v_type_x3f_262_ = lean_ctor_get(v_v_261_, 1);
lean_inc(v_type_x3f_262_);
v_idx_263_ = lean_ctor_get(v_v_261_, 2);
v___x_264_ = lean_unsigned_to_nat(0u);
v_bs_x27_265_ = lean_array_uset(v_bs_259_, v_i_258_, v___x_264_);
if (lean_obj_tag(v_type_x3f_262_) == 1)
{
lean_object* v_val_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_296_; 
v_val_277_ = lean_ctor_get(v_type_x3f_262_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_type_x3f_262_);
if (v_isSharedCheck_296_ == 0)
{
v___x_279_ = v_type_x3f_262_;
v_isShared_280_ = v_isSharedCheck_296_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_val_277_);
lean_dec(v_type_x3f_262_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_296_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_281_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
v___x_282_ = l_Lean_MessageData_ofExpr(v_val_277_);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_idx_263_, v___x_286_);
v___x_288_ = l_Nat_reprFast(v___x_287_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 3);
lean_ctor_set(v___x_279_, 0, v___x_288_);
v___x_290_ = v___x_279_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_295_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_291_ = l_Lean_MessageData_ofFormat(v___x_290_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_285_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___y_273_ = v___x_294_;
goto v___jp_272_;
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_type_x3f_262_);
v___x_297_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_idx_263_, v___x_298_);
v___x_300_ = l_Nat_reprFast(v___x_299_);
v___x_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___x_302_ = l_Lean_MessageData_ofFormat(v___x_301_);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_297_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___y_273_ = v___x_303_;
goto v___jp_272_;
}
v___jp_266_:
{
size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_i_258_, v___x_268_);
v___x_270_ = lean_array_uset(v_bs_x27_265_, v_i_258_, v___y_267_);
v_i_258_ = v___x_269_;
v_bs_259_ = v___x_270_;
goto _start;
}
v___jp_272_:
{
uint8_t v_appearsInTypeProof_274_; 
v_appearsInTypeProof_274_ = lean_ctor_get_uint8(v_v_261_, sizeof(void*)*3);
lean_dec(v_v_261_);
if (v_appearsInTypeProof_274_ == 0)
{
v___y_267_ = v___y_273_;
goto v___jp_266_;
}
else
{
lean_object* v___x_275_; lean_object* v_msg_276_; 
v___x_275_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
v_msg_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_276_, 0, v___y_273_);
lean_ctor_set(v_msg_276_, 1, v___x_275_);
v___y_267_ = v_msg_276_;
goto v___jp_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0___boxed(lean_object* v_sz_304_, lean_object* v_i_305_, lean_object* v_bs_306_){
_start:
{
size_t v_sz_boxed_307_; size_t v_i_boxed_308_; lean_object* v_res_309_; 
v_sz_boxed_307_ = lean_unbox_usize(v_sz_304_);
lean_dec(v_sz_304_);
v_i_boxed_308_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_boxed_307_, v_i_boxed_308_, v_bs_306_);
return v_res_309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(size_t v_sz_313_, size_t v_i_314_, lean_object* v_bs_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lean_usize_dec_lt(v_i_314_, v_sz_313_);
if (v___x_316_ == 0)
{
return v_bs_315_;
}
else
{
lean_object* v_v_317_; lean_object* v___x_318_; lean_object* v_bs_x27_319_; lean_object* v___x_320_; lean_object* v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v_v_317_ = lean_array_uget(v_bs_315_, v_i_314_);
v___x_318_ = lean_unsigned_to_nat(0u);
v_bs_x27_319_ = lean_array_uset(v_bs_315_, v_i_314_, v___x_318_);
v___x_320_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_v_317_);
v___x_322_ = ((size_t)1ULL);
v___x_323_ = lean_usize_add(v_i_314_, v___x_322_);
v___x_324_ = lean_array_uset(v_bs_x27_319_, v_i_314_, v___x_321_);
v_i_314_ = v___x_323_;
v_bs_315_ = v___x_324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___boxed(lean_object* v_sz_326_, lean_object* v_i_327_, lean_object* v_bs_328_){
_start:
{
size_t v_sz_boxed_329_; size_t v_i_boxed_330_; lean_object* v_res_331_; 
v_sz_boxed_329_ = lean_unbox_usize(v_sz_326_);
lean_dec(v_sz_326_);
v_i_boxed_330_ = lean_unbox_usize(v_i_327_);
lean_dec(v_i_327_);
v_res_331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_boxed_329_, v_i_boxed_330_, v_bs_328_);
return v_res_331_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0));
v___x_334_ = l_Lean_stringToMessageData(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2));
v___x_337_ = l_Lean_stringToMessageData(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(lean_object* v_declName_348_, lean_object* v_unusedInstanceBinders_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___y_352_; size_t v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; size_t v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; uint8_t v___y_387_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_array_get_size(v_unusedInstanceBinders_349_);
v___x_403_ = lean_nat_dec_lt(v___x_350_, v___x_402_);
if (v___x_403_ == 0)
{
v___y_387_ = v___x_403_;
goto v___jp_386_;
}
else
{
if (v___x_403_ == 0)
{
v___y_387_ = v___x_403_;
goto v___jp_386_;
}
else
{
size_t v___x_404_; size_t v___x_405_; uint8_t v___x_406_; 
v___x_404_ = ((size_t)0ULL);
v___x_405_ = lean_usize_of_nat(v___x_402_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_unusedInstanceBinders_349_, v___x_404_, v___x_405_);
v___y_387_ = v___x_406_;
goto v___jp_386_;
}
}
v___jp_351_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; size_t v_sz_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
lean_inc_ref(v___y_355_);
v___x_356_ = l_Lean_stringToMessageData(v___y_355_);
v___x_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_357_, 0, v___y_352_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = l_Lean_MessageData_nil;
v_sz_361_ = lean_array_size(v___y_354_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_361_, v___y_353_, v___y_354_);
v___x_363_ = lean_array_get_size(v___x_362_);
v___x_364_ = lean_nat_dec_lt(v___x_350_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec_ref(v___x_362_);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_359_);
lean_ctor_set(v___x_365_, 1, v___x_360_);
return v___x_365_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_le(v___x_363_, v___x_363_);
if (v___x_366_ == 0)
{
if (v___x_364_ == 0)
{
lean_object* v___x_367_; 
lean_dec_ref(v___x_362_);
v___x_367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_359_);
lean_ctor_set(v___x_367_, 1, v___x_360_);
return v___x_367_;
}
else
{
size_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_usize_of_nat(v___x_363_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v___x_362_, v___y_353_, v___x_368_, v___x_360_);
lean_dec_ref(v___x_362_);
v___x_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_359_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
return v___x_370_;
}
}
else
{
size_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_usize_of_nat(v___x_363_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v___x_362_, v___y_353_, v___x_371_, v___x_360_);
lean_dec_ref(v___x_362_);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_359_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
}
v___jp_374_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc_ref(v___y_379_);
v___x_380_ = l_Lean_stringToMessageData(v___y_379_);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___y_377_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
if (v___y_376_ == 0)
{
lean_object* v___x_384_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4));
v___y_352_ = v___x_383_;
v___y_353_ = v___y_375_;
v___y_354_ = v___y_378_;
v___y_355_ = v___x_384_;
goto v___jp_351_;
}
else
{
lean_object* v___x_385_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5));
v___y_352_ = v___x_383_;
v___y_353_ = v___y_375_;
v___y_354_ = v___y_378_;
v___y_355_ = v___x_385_;
goto v___jp_351_;
}
}
v___jp_386_:
{
size_t v_sz_388_; size_t v___x_389_; lean_object* v_unusedInstanceBinders_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_sz_388_ = lean_array_size(v_unusedInstanceBinders_349_);
v___x_389_ = ((size_t)0ULL);
v_unusedInstanceBinders_390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_388_, v___x_389_, v_unusedInstanceBinders_349_);
v___x_391_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7);
v___x_392_ = 0;
v___x_393_ = l_Lean_MessageData_ofConstName(v_declName_348_, v___x_392_);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_391_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_array_get_size(v_unusedInstanceBinders_390_);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_dec_eq(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10));
v___y_375_ = v___x_389_;
v___y_376_ = v___y_387_;
v___y_377_ = v___x_396_;
v___y_378_ = v_unusedInstanceBinders_390_;
v___y_379_ = v___x_400_;
goto v___jp_374_;
}
else
{
lean_object* v___x_401_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11));
v___y_375_ = v___x_389_;
v___y_376_ = v___y_387_;
v___y_377_ = v___x_396_;
v___y_378_ = v_unusedInstanceBinders_390_;
v___y_379_ = v___x_401_;
goto v___jp_374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(lean_object* v_subExpr_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___y_415_; uint8_t v___y_424_; uint8_t v___x_445_; 
v___x_445_ = l_Lean_Expr_hasFVar(v_subExpr_407_);
if (v___x_445_ == 0)
{
v___y_424_ = v___x_445_;
goto v___jp_423_;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_Expr_isSorry(v_subExpr_407_);
if (v___x_446_ == 0)
{
v___y_424_ = v___x_445_;
goto v___jp_423_;
}
else
{
uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v_subExpr_407_);
v___x_447_ = 0;
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
v___jp_414_:
{
if (lean_obj_tag(v_subExpr_407_) == 1)
{
lean_object* v_fvarId_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v___y_415_);
v_fvarId_416_ = lean_ctor_get(v_subExpr_407_, 0);
lean_inc(v_fvarId_416_);
lean_dec_ref_known(v_subExpr_407_, 1);
v___x_417_ = lean_st_ref_take(v___y_408_);
v___x_418_ = l_Lean_FVarIdSet_insert(v___x_417_, v_fvarId_416_);
v___x_419_ = lean_st_ref_put(v___y_408_, v___x_418_);
v___x_420_ = 0;
v___x_421_ = lean_box(v___x_420_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
else
{
lean_dec_ref(v_subExpr_407_);
return v___y_415_;
}
}
v___jp_423_:
{
if (v___y_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v_subExpr_407_);
v___x_425_ = lean_box(v___y_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_inc_ref(v_subExpr_407_);
v___x_427_ = l_Lean_Meta_isProof(v_subExpr_407_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_442_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_442_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___x_432_; 
v___x_432_ = lean_unbox(v_a_428_);
lean_dec(v_a_428_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_box(v___y_424_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_433_);
v___x_435_ = v___x_430_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
v___y_415_ = v___x_435_;
goto v___jp_414_;
}
}
else
{
uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
lean_dec_ref(v_subExpr_407_);
v___x_437_ = 0;
v___x_438_ = lean_box(v___x_437_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_438_);
v___x_440_ = v___x_430_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_443_; uint8_t v___x_444_; 
v_a_443_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_443_);
v___x_444_ = lean_unbox(v_a_443_);
lean_dec(v_a_443_);
if (v___x_444_ == 0)
{
lean_dec_ref(v_subExpr_407_);
return v___x_427_;
}
else
{
v___y_415_ = v___x_427_;
goto v___jp_414_;
}
}
else
{
lean_dec_ref(v_subExpr_407_);
return v___x_427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0___boxed(lean_object* v_subExpr_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(v_subExpr_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_object* v_00_u03b1_458_, lean_object* v_x_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_apply_1(v_x_459_, lean_box(0));
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_468_, lean_object* v_x_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(v_00_u03b1_468_, v_x_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc(v___y_482_);
lean_inc_ref(v___y_481_);
lean_inc(v___y_479_);
lean_inc(v___y_478_);
v___x_486_ = lean_apply_8(v_k_477_, v_b_480_, v___y_478_, v___y_479_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, lean_box(0));
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v_b_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(v_k_487_, v___y_488_, v___y_489_, v_b_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_489_);
lean_dec(v___y_488_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_name_497_, uint8_t v_bi_498_, lean_object* v_type_499_, lean_object* v_k_500_, uint8_t v_kind_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___f_509_; lean_object* v___x_510_; 
lean_inc(v___y_503_);
lean_inc(v___y_502_);
v___f_509_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_509_, 0, v_k_500_);
lean_closure_set(v___f_509_, 1, v___y_502_);
lean_closure_set(v___f_509_, 2, v___y_503_);
v___x_510_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_497_, v_bi_498_, v_type_499_, v___f_509_, v_kind_501_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_510_) == 0)
{
return v___x_510_;
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_519_, lean_object* v_bi_520_, lean_object* v_type_521_, lean_object* v_k_522_, lean_object* v_kind_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
uint8_t v_bi_boxed_531_; uint8_t v_kind_boxed_532_; lean_object* v_res_533_; 
v_bi_boxed_531_ = lean_unbox(v_bi_520_);
v_kind_boxed_532_ = lean_unbox(v_kind_523_);
v_res_533_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_519_, v_bi_boxed_531_, v_type_521_, v_k_522_, v_kind_boxed_532_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec(v___y_524_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_534_, lean_object* v_f_535_, lean_object* v_body_536_, lean_object* v_x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(v_fvars_534_, v_f_535_, v_body_536_, v_x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec(v___y_538_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(lean_object* v_f_546_, lean_object* v_fvars_547_, lean_object* v_a_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
if (lean_obj_tag(v_a_548_) == 7)
{
lean_object* v_binderName_556_; lean_object* v_binderType_557_; lean_object* v_body_558_; uint8_t v_binderInfo_559_; lean_object* v_d_560_; lean_object* v___x_561_; 
v_binderName_556_ = lean_ctor_get(v_a_548_, 0);
lean_inc(v_binderName_556_);
v_binderType_557_ = lean_ctor_get(v_a_548_, 1);
lean_inc_ref(v_binderType_557_);
v_body_558_ = lean_ctor_get(v_a_548_, 2);
lean_inc_ref(v_body_558_);
v_binderInfo_559_ = lean_ctor_get_uint8(v_a_548_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_548_, 3);
v_d_560_ = lean_expr_instantiate_rev(v_binderType_557_, v_fvars_547_);
lean_dec_ref(v_binderType_557_);
lean_inc_ref(v_f_546_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
lean_inc(v___y_549_);
lean_inc_ref(v_d_560_);
v___x_561_ = lean_apply_8(v_f_546_, v_d_560_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, lean_box(0));
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___f_562_; uint8_t v___x_563_; lean_object* v___x_564_; 
lean_dec_ref_known(v___x_561_, 1);
v___f_562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed), 11, 3);
lean_closure_set(v___f_562_, 0, v_fvars_547_);
lean_closure_set(v___f_562_, 1, v_f_546_);
lean_closure_set(v___f_562_, 2, v_body_558_);
v___x_563_ = 0;
v___x_564_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_556_, v_binderInfo_559_, v_d_560_, v___f_562_, v___x_563_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_564_;
}
else
{
lean_dec_ref(v_d_560_);
lean_dec_ref(v_body_558_);
lean_dec(v_binderName_556_);
lean_dec_ref(v_fvars_547_);
lean_dec_ref(v_f_546_);
return v___x_561_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_expr_instantiate_rev(v_a_548_, v_fvars_547_);
lean_dec_ref(v_fvars_547_);
lean_dec_ref(v_a_548_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
lean_inc(v___y_549_);
v___x_566_ = lean_apply_8(v_f_546_, v___x_565_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, lean_box(0));
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(lean_object* v_fvars_567_, lean_object* v_f_568_, lean_object* v_body_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_array_push(v_fvars_567_, v_x_570_);
v___x_579_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_568_, v___x_578_, v_body_569_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_f_580_, lean_object* v_fvars_581_, lean_object* v_a_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_580_, v_fvars_581_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec(v___y_583_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(lean_object* v_f_593_, lean_object* v_e_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_603_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_593_, v___x_602_, v_e_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___boxed(lean_object* v_f_604_, lean_object* v_e_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v_f_604_, v_e_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v___y_606_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
return v_x_614_;
}
else
{
lean_object* v_key_616_; lean_object* v_value_617_; lean_object* v_tail_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_641_; 
v_key_616_ = lean_ctor_get(v_x_615_, 0);
v_value_617_ = lean_ctor_get(v_x_615_, 1);
v_tail_618_ = lean_ctor_get(v_x_615_, 2);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_641_ == 0)
{
v___x_620_ = v_x_615_;
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_tail_618_);
lean_inc(v_value_617_);
lean_inc(v_key_616_);
lean_dec(v_x_615_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_641_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; uint64_t v___x_623_; uint64_t v___x_624_; uint64_t v___x_625_; uint64_t v_fold_626_; uint64_t v___x_627_; uint64_t v___x_628_; uint64_t v___x_629_; size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_622_ = lean_array_get_size(v_x_614_);
v___x_623_ = l_Lean_Expr_hash(v_key_616_);
v___x_624_ = 32ULL;
v___x_625_ = lean_uint64_shift_right(v___x_623_, v___x_624_);
v_fold_626_ = lean_uint64_xor(v___x_623_, v___x_625_);
v___x_627_ = 16ULL;
v___x_628_ = lean_uint64_shift_right(v_fold_626_, v___x_627_);
v___x_629_ = lean_uint64_xor(v_fold_626_, v___x_628_);
v___x_630_ = lean_uint64_to_usize(v___x_629_);
v___x_631_ = lean_usize_of_nat(v___x_622_);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_sub(v___x_631_, v___x_632_);
v___x_634_ = lean_usize_land(v___x_630_, v___x_633_);
v___x_635_ = lean_array_uget_borrowed(v_x_614_, v___x_634_);
lean_inc(v___x_635_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 2, v___x_635_);
v___x_637_ = v___x_620_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_key_616_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_value_617_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v___x_635_);
v___x_637_ = v_reuseFailAlloc_640_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
v___x_638_ = lean_array_uset(v_x_614_, v___x_634_, v___x_637_);
v_x_614_ = v___x_638_;
v_x_615_ = v_tail_618_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_i_642_, lean_object* v_source_643_, lean_object* v_target_644_){
_start:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_array_get_size(v_source_643_);
v___x_646_ = lean_nat_dec_lt(v_i_642_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec_ref(v_source_643_);
lean_dec(v_i_642_);
return v_target_644_;
}
else
{
lean_object* v_es_647_; lean_object* v___x_648_; lean_object* v_source_649_; lean_object* v_target_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_es_647_ = lean_array_fget(v_source_643_, v_i_642_);
v___x_648_ = lean_box(0);
v_source_649_ = lean_array_fset(v_source_643_, v_i_642_, v___x_648_);
v_target_650_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_target_644_, v_es_647_);
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_nat_add(v_i_642_, v___x_651_);
lean_dec(v_i_642_);
v_i_642_ = v___x_652_;
v_source_643_ = v_source_649_;
v_target_644_ = v_target_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_data_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_nbuckets_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_655_ = lean_array_get_size(v_data_654_);
v___x_656_ = lean_unsigned_to_nat(2u);
v_nbuckets_657_ = lean_nat_mul(v___x_655_, v___x_656_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_box(0);
v___x_660_ = lean_mk_array(v_nbuckets_657_, v___x_659_);
v___x_661_ = lean_array_propagate_mark(v_data_654_, v___x_660_);
v___x_662_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v___x_658_, v_data_654_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_a_663_, lean_object* v_b_664_, lean_object* v_x_665_){
_start:
{
if (lean_obj_tag(v_x_665_) == 0)
{
lean_dec(v_b_664_);
lean_dec_ref(v_a_663_);
return v_x_665_;
}
else
{
lean_object* v_key_666_; lean_object* v_value_667_; lean_object* v_tail_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_680_; 
v_key_666_ = lean_ctor_get(v_x_665_, 0);
v_value_667_ = lean_ctor_get(v_x_665_, 1);
v_tail_668_ = lean_ctor_get(v_x_665_, 2);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_680_ == 0)
{
v___x_670_ = v_x_665_;
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_tail_668_);
lean_inc(v_value_667_);
lean_inc(v_key_666_);
lean_dec(v_x_665_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_680_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
uint8_t v___x_672_; 
v___x_672_ = lean_expr_eqv(v_key_666_, v_a_663_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_663_, v_b_664_, v_tail_668_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 2, v___x_673_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_key_666_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_value_667_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec(v_value_667_);
lean_dec(v_key_666_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_b_664_);
lean_ctor_set(v___x_670_, 0, v_a_663_);
v___x_678_ = v___x_670_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_663_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_b_664_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_tail_668_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_a_681_, lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_682_) == 0)
{
uint8_t v___x_683_; 
v___x_683_ = 0;
return v___x_683_;
}
else
{
lean_object* v_key_684_; lean_object* v_tail_685_; uint8_t v___x_686_; 
v_key_684_ = lean_ctor_get(v_x_682_, 0);
v_tail_685_ = lean_ctor_get(v_x_682_, 2);
v___x_686_ = lean_expr_eqv(v_key_684_, v_a_681_);
if (v___x_686_ == 0)
{
v_x_682_ = v_tail_685_;
goto _start;
}
else
{
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_a_688_, lean_object* v_x_689_){
_start:
{
uint8_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_688_, v_x_689_);
lean_dec(v_x_689_);
lean_dec_ref(v_a_688_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(lean_object* v_m_692_, lean_object* v_a_693_, lean_object* v_b_694_){
_start:
{
lean_object* v_size_695_; lean_object* v_buckets_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_739_; 
v_size_695_ = lean_ctor_get(v_m_692_, 0);
v_buckets_696_ = lean_ctor_get(v_m_692_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_m_692_);
if (v_isSharedCheck_739_ == 0)
{
v___x_698_ = v_m_692_;
v_isShared_699_ = v_isSharedCheck_739_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_buckets_696_);
lean_inc(v_size_695_);
lean_dec(v_m_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_739_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v_fold_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v_bkt_713_; uint8_t v___x_714_; 
v___x_700_ = lean_array_get_size(v_buckets_696_);
v___x_701_ = l_Lean_Expr_hash(v_a_693_);
v___x_702_ = 32ULL;
v___x_703_ = lean_uint64_shift_right(v___x_701_, v___x_702_);
v_fold_704_ = lean_uint64_xor(v___x_701_, v___x_703_);
v___x_705_ = 16ULL;
v___x_706_ = lean_uint64_shift_right(v_fold_704_, v___x_705_);
v___x_707_ = lean_uint64_xor(v_fold_704_, v___x_706_);
v___x_708_ = lean_uint64_to_usize(v___x_707_);
v___x_709_ = lean_usize_of_nat(v___x_700_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_sub(v___x_709_, v___x_710_);
v___x_712_ = lean_usize_land(v___x_708_, v___x_711_);
v_bkt_713_ = lean_array_uget_borrowed(v_buckets_696_, v___x_712_);
v___x_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_693_, v_bkt_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v_size_x27_716_; lean_object* v___x_717_; lean_object* v_buckets_x27_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v_size_x27_716_ = lean_nat_add(v_size_695_, v___x_715_);
lean_dec(v_size_695_);
lean_inc(v_bkt_713_);
v___x_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_717_, 0, v_a_693_);
lean_ctor_set(v___x_717_, 1, v_b_694_);
lean_ctor_set(v___x_717_, 2, v_bkt_713_);
v_buckets_x27_718_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(4u);
v___x_720_ = lean_nat_mul(v_size_x27_716_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(3u);
v___x_722_ = lean_nat_div(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_array_get_size(v_buckets_x27_718_);
v___x_724_ = lean_nat_dec_le(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v_val_725_; lean_object* v___x_727_; 
v_val_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_buckets_x27_718_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_val_725_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_727_ = v___x_698_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_val_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_730_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_buckets_x27_718_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_730_ = v___x_698_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_buckets_x27_718_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_732_; lean_object* v_buckets_x27_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc(v_bkt_713_);
v___x_732_ = lean_box(0);
v_buckets_x27_733_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_732_);
v___x_734_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_693_, v_b_694_, v_bkt_713_);
v___x_735_ = lean_array_uset(v_buckets_x27_733_, v___x_712_, v___x_734_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_735_);
v___x_737_ = v___x_698_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_size_695_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(lean_object* v_a_740_, lean_object* v_e_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_744_ = lean_st_ref_take(v_a_740_);
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v___x_744_, v_e_741_, v_a_742_);
v___x_746_ = lean_st_ref_put(v_a_740_, v___x_745_);
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed(lean_object* v_a_748_, lean_object* v_e_749_, lean_object* v_a_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(v_a_748_, v_e_749_, v_a_750_);
lean_dec(v_a_748_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(lean_object* v_name_753_, lean_object* v_type_754_, lean_object* v_val_755_, lean_object* v_k_756_, uint8_t v_nondep_757_, uint8_t v_kind_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___f_766_; lean_object* v___x_767_; 
lean_inc(v___y_760_);
lean_inc(v___y_759_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_766_, 0, v_k_756_);
lean_closure_set(v___f_766_, 1, v___y_759_);
lean_closure_set(v___f_766_, 2, v___y_760_);
v___x_767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_753_, v_type_754_, v_val_755_, v___f_766_, v_nondep_757_, v_kind_758_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_767_) == 0)
{
return v___x_767_;
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg___boxed(lean_object* v_name_776_, lean_object* v_type_777_, lean_object* v_val_778_, lean_object* v_k_779_, lean_object* v_nondep_780_, lean_object* v_kind_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v_nondep_boxed_789_; uint8_t v_kind_boxed_790_; lean_object* v_res_791_; 
v_nondep_boxed_789_ = lean_unbox(v_nondep_780_);
v_kind_boxed_790_ = lean_unbox(v_kind_781_);
v_res_791_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_776_, v_type_777_, v_val_778_, v_k_779_, v_nondep_boxed_789_, v_kind_boxed_790_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec(v___y_782_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed(lean_object* v_fvars_792_, lean_object* v_f_793_, lean_object* v_body_794_, lean_object* v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(v_fvars_792_, v_f_793_, v_body_794_, v_x_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(lean_object* v_f_804_, lean_object* v_fvars_805_, lean_object* v_a_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
if (lean_obj_tag(v_a_806_) == 8)
{
lean_object* v_declName_814_; lean_object* v_type_815_; lean_object* v_value_816_; lean_object* v_body_817_; lean_object* v_d_818_; lean_object* v___x_819_; 
v_declName_814_ = lean_ctor_get(v_a_806_, 0);
lean_inc(v_declName_814_);
v_type_815_ = lean_ctor_get(v_a_806_, 1);
lean_inc_ref(v_type_815_);
v_value_816_ = lean_ctor_get(v_a_806_, 2);
lean_inc_ref(v_value_816_);
v_body_817_ = lean_ctor_get(v_a_806_, 3);
lean_inc_ref(v_body_817_);
lean_dec_ref_known(v_a_806_, 4);
v_d_818_ = lean_expr_instantiate_rev(v_type_815_, v_fvars_805_);
lean_dec_ref(v_type_815_);
lean_inc_ref(v_f_804_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc(v___y_807_);
lean_inc_ref(v_d_818_);
v___x_819_ = lean_apply_8(v_f_804_, v_d_818_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_v_820_; lean_object* v___x_821_; 
lean_dec_ref_known(v___x_819_, 1);
v_v_820_ = lean_expr_instantiate_rev(v_value_816_, v_fvars_805_);
lean_dec_ref(v_value_816_);
lean_inc_ref(v_f_804_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc(v___y_807_);
lean_inc_ref(v_v_820_);
v___x_821_ = lean_apply_8(v_f_804_, v_v_820_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___f_822_; uint8_t v___x_823_; uint8_t v___x_824_; lean_object* v___x_825_; 
lean_dec_ref_known(v___x_821_, 1);
v___f_822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed), 11, 3);
lean_closure_set(v___f_822_, 0, v_fvars_805_);
lean_closure_set(v___f_822_, 1, v_f_804_);
lean_closure_set(v___f_822_, 2, v_body_817_);
v___x_823_ = 0;
v___x_824_ = 0;
v___x_825_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_declName_814_, v_d_818_, v_v_820_, v___f_822_, v___x_823_, v___x_824_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
return v___x_825_;
}
else
{
lean_dec_ref(v_v_820_);
lean_dec_ref(v_d_818_);
lean_dec_ref(v_body_817_);
lean_dec(v_declName_814_);
lean_dec_ref(v_fvars_805_);
lean_dec_ref(v_f_804_);
return v___x_821_;
}
}
else
{
lean_dec_ref(v_d_818_);
lean_dec_ref(v_body_817_);
lean_dec_ref(v_value_816_);
lean_dec(v_declName_814_);
lean_dec_ref(v_fvars_805_);
lean_dec_ref(v_f_804_);
return v___x_819_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_expr_instantiate_rev(v_a_806_, v_fvars_805_);
lean_dec_ref(v_fvars_805_);
lean_dec_ref(v_a_806_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc(v___y_807_);
v___x_827_ = lean_apply_8(v_f_804_, v___x_826_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(lean_object* v_fvars_828_, lean_object* v_f_829_, lean_object* v_body_830_, lean_object* v_x_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_array_push(v_fvars_828_, v_x_831_);
v___x_840_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_829_, v___x_839_, v_body_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___boxed(lean_object* v_f_841_, lean_object* v_fvars_842_, lean_object* v_a_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_841_, v_fvars_842_, v_a_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec(v___y_844_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(lean_object* v_f_852_, lean_object* v_e_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_862_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_852_, v___x_861_, v_e_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5___boxed(lean_object* v_f_863_, lean_object* v_e_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v_f_863_, v_e_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec(v___y_865_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_873_, lean_object* v_f_874_, lean_object* v_body_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(v_fvars_873_, v_f_874_, v_body_875_, v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec(v___y_877_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(lean_object* v_f_885_, lean_object* v_fvars_886_, lean_object* v_a_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
if (lean_obj_tag(v_a_887_) == 6)
{
lean_object* v_binderName_895_; lean_object* v_binderType_896_; lean_object* v_body_897_; uint8_t v_binderInfo_898_; lean_object* v_d_899_; lean_object* v___x_900_; 
v_binderName_895_ = lean_ctor_get(v_a_887_, 0);
lean_inc(v_binderName_895_);
v_binderType_896_ = lean_ctor_get(v_a_887_, 1);
lean_inc_ref(v_binderType_896_);
v_body_897_ = lean_ctor_get(v_a_887_, 2);
lean_inc_ref(v_body_897_);
v_binderInfo_898_ = lean_ctor_get_uint8(v_a_887_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_887_, 3);
v_d_899_ = lean_expr_instantiate_rev(v_binderType_896_, v_fvars_886_);
lean_dec_ref(v_binderType_896_);
lean_inc_ref(v_f_885_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v_d_899_);
v___x_900_ = lean_apply_8(v_f_885_, v_d_899_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, lean_box(0));
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___f_901_; uint8_t v___x_902_; lean_object* v___x_903_; 
lean_dec_ref_known(v___x_900_, 1);
v___f_901_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed), 11, 3);
lean_closure_set(v___f_901_, 0, v_fvars_886_);
lean_closure_set(v___f_901_, 1, v_f_885_);
lean_closure_set(v___f_901_, 2, v_body_897_);
v___x_902_ = 0;
v___x_903_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_895_, v_binderInfo_898_, v_d_899_, v___f_901_, v___x_902_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
return v___x_903_;
}
else
{
lean_dec_ref(v_d_899_);
lean_dec_ref(v_body_897_);
lean_dec(v_binderName_895_);
lean_dec_ref(v_fvars_886_);
lean_dec_ref(v_f_885_);
return v___x_900_;
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_expr_instantiate_rev(v_a_887_, v_fvars_886_);
lean_dec_ref(v_fvars_886_);
lean_dec_ref(v_a_887_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
lean_inc(v___y_888_);
v___x_905_ = lean_apply_8(v_f_885_, v___x_904_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, lean_box(0));
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(lean_object* v_fvars_906_, lean_object* v_f_907_, lean_object* v_body_908_, lean_object* v_x_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_array_push(v_fvars_906_, v_x_909_);
v___x_918_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_907_, v___x_917_, v_body_908_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_f_919_, lean_object* v_fvars_920_, lean_object* v_a_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_919_, v_fvars_920_, v_a_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec(v___y_922_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(lean_object* v_f_930_, lean_object* v_e_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_940_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_930_, v___x_939_, v_e_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4___boxed(lean_object* v_f_941_, lean_object* v_e_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v_f_941_, v_e_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_943_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_951_, lean_object* v_x_952_){
_start:
{
if (lean_obj_tag(v_x_952_) == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_box(0);
return v___x_953_;
}
else
{
lean_object* v_key_954_; lean_object* v_value_955_; lean_object* v_tail_956_; uint8_t v___x_957_; 
v_key_954_ = lean_ctor_get(v_x_952_, 0);
v_value_955_ = lean_ctor_get(v_x_952_, 1);
v_tail_956_ = lean_ctor_get(v_x_952_, 2);
v___x_957_ = lean_expr_eqv(v_key_954_, v_a_951_);
if (v___x_957_ == 0)
{
v_x_952_ = v_tail_956_;
goto _start;
}
else
{
lean_object* v___x_959_; 
lean_inc(v_value_955_);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v_value_955_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_960_, lean_object* v_x_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_960_, v_x_961_);
lean_dec(v_x_961_);
lean_dec_ref(v_a_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(lean_object* v_m_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_buckets_965_; lean_object* v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v_fold_970_; uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_buckets_965_ = lean_ctor_get(v_m_963_, 1);
v___x_966_ = lean_array_get_size(v_buckets_965_);
v___x_967_ = l_Lean_Expr_hash(v_a_964_);
v___x_968_ = 32ULL;
v___x_969_ = lean_uint64_shift_right(v___x_967_, v___x_968_);
v_fold_970_ = lean_uint64_xor(v___x_967_, v___x_969_);
v___x_971_ = 16ULL;
v___x_972_ = lean_uint64_shift_right(v_fold_970_, v___x_971_);
v___x_973_ = lean_uint64_xor(v_fold_970_, v___x_972_);
v___x_974_ = lean_uint64_to_usize(v___x_973_);
v___x_975_ = lean_usize_of_nat(v___x_966_);
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_sub(v___x_975_, v___x_976_);
v___x_978_ = lean_usize_land(v___x_974_, v___x_977_);
v___x_979_ = lean_array_uget_borrowed(v_buckets_965_, v___x_978_);
v___x_980_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_964_, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_981_, v_a_982_);
lean_dec_ref(v_a_982_);
lean_dec_ref(v_m_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_984_, lean_object* v_x_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_apply_1(v_x_985_, lean_box(0));
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(v_00_u03b1_994_, v_x_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed(lean_object* v_fn_1003_, lean_object* v_e_1004_, lean_object* v_a_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1003_, v_e_1004_, v_a_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec(v_a_1005_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(lean_object* v_fn_1013_, lean_object* v_e_1014_, lean_object* v_a_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_a_1023_; lean_object* v___y_1035_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_inc(v_a_1015_);
v___x_1037_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1037_, 0, lean_box(0));
lean_closure_set(v___x_1037_, 1, lean_box(0));
lean_closure_set(v___x_1037_, 2, v_a_1015_);
v___x_1038_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_box(0), v___x_1037_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1075_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1075_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1075_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_a_1039_, v_e_1014_);
lean_dec(v_a_1039_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; 
lean_del_object(v___x_1041_);
lean_inc_ref(v_fn_1013_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v_e_1014_);
v___x_1044_ = lean_apply_7(v_fn_1013_, v_e_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; uint8_t v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = lean_unbox(v_a_1045_);
lean_dec(v_a_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref(v_fn_1013_);
v___x_1047_ = lean_box(0);
v_a_1023_ = v___x_1047_;
goto v___jp_1022_;
}
else
{
switch(lean_obj_tag(v_e_1014_))
{
case 7:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1048_, 0, v_fn_1013_);
lean_inc_ref(v_e_1014_);
v___x_1049_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v___x_1048_, v_e_1014_, v_a_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
v___y_1035_ = v___x_1049_;
goto v___jp_1034_;
}
case 6:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1050_, 0, v_fn_1013_);
lean_inc_ref(v_e_1014_);
v___x_1051_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v___x_1050_, v_e_1014_, v_a_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
v___y_1035_ = v___x_1051_;
goto v___jp_1034_;
}
case 8:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1052_, 0, v_fn_1013_);
lean_inc_ref(v_e_1014_);
v___x_1053_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v___x_1052_, v_e_1014_, v_a_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
v___y_1035_ = v___x_1053_;
goto v___jp_1034_;
}
case 5:
{
lean_object* v_fn_1054_; lean_object* v_arg_1055_; lean_object* v___x_1056_; 
v_fn_1054_ = lean_ctor_get(v_e_1014_, 0);
v_arg_1055_ = lean_ctor_get(v_e_1014_, 1);
lean_inc_ref(v_fn_1054_);
lean_inc_ref(v_fn_1013_);
v___x_1056_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1013_, v_fn_1054_, v_a_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref_known(v___x_1056_, 1);
lean_inc_ref(v_arg_1055_);
v___x_1057_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1013_, v_arg_1055_, v_a_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
v___y_1035_ = v___x_1057_;
goto v___jp_1034_;
}
else
{
lean_dec_ref(v_fn_1013_);
v___y_1035_ = v___x_1056_;
goto v___jp_1034_;
}
}
case 10:
{
lean_object* v_expr_1058_; lean_object* v___x_1059_; 
v_expr_1058_ = lean_ctor_get(v_e_1014_, 1);
lean_inc_ref(v_expr_1058_);
v___x_1059_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1013_, v_expr_1058_, v_a_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
v___y_1035_ = v___x_1059_;
goto v___jp_1034_;
}
case 11:
{
lean_object* v_struct_1060_; lean_object* v___x_1061_; 
v_struct_1060_ = lean_ctor_get(v_e_1014_, 2);
lean_inc_ref(v_struct_1060_);
v___x_1061_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1013_, v_struct_1060_, v_a_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
v___y_1035_ = v___x_1061_;
goto v___jp_1034_;
}
default: 
{
lean_object* v___x_1062_; 
lean_dec_ref(v_fn_1013_);
v___x_1062_ = lean_box(0);
v_a_1023_ = v___x_1062_;
goto v___jp_1022_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_e_1014_);
lean_dec_ref(v_fn_1013_);
v_a_1063_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1044_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1044_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_val_1071_; lean_object* v___x_1073_; 
lean_dec_ref(v_e_1014_);
lean_dec_ref(v_fn_1013_);
v_val_1071_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1071_);
lean_dec_ref_known(v___x_1043_, 1);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v_val_1071_);
v___x_1073_ = v___x_1041_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_val_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec_ref(v_e_1014_);
lean_dec_ref(v_fn_1013_);
v_a_1076_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1038_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1038_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
v___jp_1022_:
{
lean_object* v___f_1024_; lean_object* v___x_1025_; 
lean_inc(v_a_1015_);
v___f_1024_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1024_, 0, v_a_1015_);
lean_closure_set(v___f_1024_, 1, v_e_1014_);
lean_closure_set(v___f_1024_, 2, v_a_1023_);
v___x_1025_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_box(0), v___f_1024_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___x_1025_, 0);
lean_dec(v_unused_1033_);
v___x_1027_ = v___x_1025_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v___x_1025_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v_a_1023_);
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1023_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
else
{
return v___x_1025_;
}
}
v___jp_1034_:
{
if (lean_obj_tag(v___y_1035_) == 0)
{
lean_object* v_a_1036_; 
v_a_1036_ = lean_ctor_get(v___y_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___y_1035_, 1);
v_a_1023_ = v_a_1036_;
goto v___jp_1022_;
}
else
{
lean_dec_ref(v_e_1014_);
return v___y_1035_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_unsigned_to_nat(16u);
v___x_1086_ = lean_mk_array(v___x_1085_, v___x_1084_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v___x_1087_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1);
v___x_1091_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1091_, 0, lean_box(0));
lean_closure_set(v___x_1091_, 1, lean_box(0));
lean_closure_set(v___x_1091_, 2, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(lean_object* v_input_1092_, lean_object* v_fn_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_a_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2);
v___x_1101_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_box(0), v___x_1100_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1093_, v_input_1092_, v_a_1102_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1105_, 0, lean_box(0));
lean_closure_set(v___x_1105_, 1, lean_box(0));
lean_closure_set(v___x_1105_, 2, v_a_1102_);
v___x_1106_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_box(0), v___x_1105_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v___x_1106_, 0);
lean_dec(v_unused_1114_);
v___x_1108_ = v___x_1106_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v___x_1106_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v_a_1104_);
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1104_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_dec(v_a_1102_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___boxed(lean_object* v_input_1115_, lean_object* v_fn_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_input_1115_, v_fn_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(lean_object* v_e_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1132_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0));
v___x_1133_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_e_1125_, v___f_1132_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___boxed(lean_object* v_e_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1142_, lean_object* v_m_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_1143_, v_a_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1146_, lean_object* v_m_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(v_00_u03b2_1146_, v_m_1147_, v_a_1148_);
lean_dec_ref(v_a_1148_);
lean_dec_ref(v_m_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1150_, lean_object* v_m_1151_, lean_object* v_a_1152_, lean_object* v_b_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v_m_1151_, v_a_1152_, v_b_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1155_, lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1156_, v_x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1159_, lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1159_, v_a_1160_, v_x_1161_);
lean_dec(v_x_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1163_, lean_object* v_a_1164_, lean_object* v_x_1165_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_1164_, v_x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1167_, lean_object* v_a_1168_, lean_object* v_x_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1167_, v_a_1168_, v_x_1169_);
lean_dec(v_x_1169_);
lean_dec_ref(v_a_1168_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1172_, lean_object* v_data_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_data_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1175_, lean_object* v_a_1176_, lean_object* v_b_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_1176_, v_b_1177_, v_x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_1180_, lean_object* v_name_1181_, uint8_t v_bi_1182_, lean_object* v_type_1183_, lean_object* v_k_1184_, uint8_t v_kind_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_1181_, v_bi_1182_, v_type_1183_, v_k_1184_, v_kind_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_name_1195_, lean_object* v_bi_1196_, lean_object* v_type_1197_, lean_object* v_k_1198_, lean_object* v_kind_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v_bi_boxed_1207_; uint8_t v_kind_boxed_1208_; lean_object* v_res_1209_; 
v_bi_boxed_1207_ = lean_unbox(v_bi_1196_);
v_kind_boxed_1208_ = lean_unbox(v_kind_1199_);
v_res_1209_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_1194_, v_name_1195_, v_bi_boxed_1207_, v_type_1197_, v_k_1198_, v_kind_boxed_1208_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec(v___y_1200_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(lean_object* v_00_u03b1_1210_, lean_object* v_name_1211_, lean_object* v_type_1212_, lean_object* v_val_1213_, lean_object* v_k_1214_, uint8_t v_nondep_1215_, uint8_t v_kind_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_1211_, v_type_1212_, v_val_1213_, v_k_1214_, v_nondep_1215_, v_kind_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_name_1226_, lean_object* v_type_1227_, lean_object* v_val_1228_, lean_object* v_k_1229_, lean_object* v_nondep_1230_, lean_object* v_kind_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v_nondep_boxed_1239_; uint8_t v_kind_boxed_1240_; lean_object* v_res_1241_; 
v_nondep_boxed_1239_ = lean_unbox(v_nondep_1230_);
v_kind_boxed_1240_ = lean_unbox(v_kind_1231_);
v_res_1241_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(v_00_u03b1_1225_, v_name_1226_, v_type_1227_, v_val_1228_, v_k_1229_, v_nondep_boxed_1239_, v_kind_boxed_1240_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1242_, lean_object* v_i_1243_, lean_object* v_source_1244_, lean_object* v_target_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_i_1243_, v_source_1244_, v_target_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10(lean_object* v_00_u03b2_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_x_1248_, v_x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(lean_object* v_k_1251_, lean_object* v___y_1252_, lean_object* v_b_1253_, lean_object* v_c_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
lean_inc(v___y_1256_);
lean_inc_ref(v___y_1255_);
lean_inc(v___y_1252_);
v___x_1260_ = lean_apply_8(v_k_1251_, v_b_1253_, v_c_1254_, v___y_1252_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, lean_box(0));
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_1261_, lean_object* v___y_1262_, lean_object* v_b_1263_, lean_object* v_c_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(v_k_1261_, v___y_1262_, v_b_1263_, v_c_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1262_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(lean_object* v_type_1271_, lean_object* v_maxFVars_x3f_1272_, lean_object* v_k_1273_, uint8_t v_cleanupAnnotations_1274_, uint8_t v_whnfType_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___f_1282_; lean_object* v___x_1283_; 
lean_inc(v___y_1276_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1282_, 0, v_k_1273_);
lean_closure_set(v___f_1282_, 1, v___y_1276_);
v___x_1283_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1271_, v_maxFVars_x3f_1272_, v___f_1282_, v_cleanupAnnotations_1274_, v_whnfType_1275_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1283_) == 0)
{
return v___x_1283_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___boxed(lean_object* v_type_1292_, lean_object* v_maxFVars_x3f_1293_, lean_object* v_k_1294_, lean_object* v_cleanupAnnotations_1295_, lean_object* v_whnfType_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1303_; uint8_t v_whnfType_boxed_1304_; lean_object* v_res_1305_; 
v_cleanupAnnotations_boxed_1303_ = lean_unbox(v_cleanupAnnotations_1295_);
v_whnfType_boxed_1304_ = lean_unbox(v_whnfType_1296_);
v_res_1305_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_1292_, v_maxFVars_x3f_1293_, v_k_1294_, v_cleanupAnnotations_boxed_1303_, v_whnfType_boxed_1304_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(lean_object* v_00_u03b1_1306_, lean_object* v_type_1307_, lean_object* v_maxFVars_x3f_1308_, lean_object* v_k_1309_, uint8_t v_cleanupAnnotations_1310_, uint8_t v_whnfType_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_1307_, v_maxFVars_x3f_1308_, v_k_1309_, v_cleanupAnnotations_1310_, v_whnfType_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___boxed(lean_object* v_00_u03b1_1319_, lean_object* v_type_1320_, lean_object* v_maxFVars_x3f_1321_, lean_object* v_k_1322_, lean_object* v_cleanupAnnotations_1323_, lean_object* v_whnfType_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1331_; uint8_t v_whnfType_boxed_1332_; lean_object* v_res_1333_; 
v_cleanupAnnotations_boxed_1331_ = lean_unbox(v_cleanupAnnotations_1323_);
v_whnfType_boxed_1332_ = lean_unbox(v_whnfType_1324_);
v_res_1333_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(v_00_u03b1_1319_, v_type_1320_, v_maxFVars_x3f_1321_, v_k_1322_, v_cleanupAnnotations_boxed_1331_, v_whnfType_boxed_1332_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed(lean_object* v___x_1334_, lean_object* v_currentBinderIdx_1335_, lean_object* v___x_1336_, lean_object* v_currentFVars_1337_, lean_object* v_p_1338_, lean_object* v_fvar_1339_, lean_object* v_e_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(v___x_1334_, v_currentBinderIdx_1335_, v___x_1336_, v_currentFVars_1337_, v_p_1338_, v_fvar_1339_, v_e_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v_fvar_1339_);
lean_dec(v___x_1336_);
lean_dec_ref(v___x_1334_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(lean_object* v_p_1350_, lean_object* v_e_1351_, lean_object* v_currentBinderIdx_1352_, lean_object* v_currentFVars_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_e_1360_; uint8_t v___x_1361_; 
v_e_1360_ = l_Lean_Expr_cleanupAnnotations(v_e_1351_);
v___x_1361_ = l_Lean_Expr_isForall(v_e_1360_);
if (v___x_1361_ == 0)
{
if (lean_obj_tag(v_e_1360_) == 8)
{
lean_object* v_type_1362_; lean_object* v_body_1363_; lean_object* v___x_1364_; 
v_type_1362_ = lean_ctor_get(v_e_1360_, 1);
lean_inc_ref_n(v_type_1362_, 2);
v_body_1363_ = lean_ctor_get(v_e_1360_, 3);
lean_inc_ref(v_body_1363_);
lean_dec_ref_known(v_e_1360_, 4);
v___x_1364_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_type_1362_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref_known(v___x_1364_, 1);
v___x_1365_ = l_Lean_Meta_mkSorry(v_type_1362_, v___x_1361_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = lean_expr_instantiate1(v_body_1363_, v_a_1366_);
lean_dec(v_a_1366_);
lean_dec_ref(v_body_1363_);
v_e_1351_ = v___x_1367_;
goto _start;
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec_ref(v_body_1363_);
lean_dec_ref(v_currentFVars_1353_);
lean_dec(v_currentBinderIdx_1352_);
lean_dec_ref(v_p_1350_);
v_a_1369_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1365_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1365_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_body_1363_);
lean_dec_ref(v_type_1362_);
lean_dec_ref(v_currentFVars_1353_);
lean_dec(v_currentBinderIdx_1352_);
lean_dec_ref(v_p_1350_);
v_a_1377_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1364_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1364_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v___x_1385_; 
lean_dec(v_currentBinderIdx_1352_);
lean_dec_ref(v_p_1350_);
v___x_1385_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_1360_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1393_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v_currentFVars_1353_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_currentFVars_1353_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v_currentFVars_1353_);
v_a_1394_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1385_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1385_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
else
{
lean_object* v_binderType_1402_; lean_object* v___x_1403_; 
v_binderType_1402_ = lean_ctor_get(v_e_1360_, 1);
lean_inc_ref_n(v_binderType_1402_, 2);
v___x_1403_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_binderType_1402_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v___x_1404_; uint8_t v___y_1406_; uint8_t v___x_1427_; uint8_t v___x_1428_; 
lean_dec_ref_known(v___x_1403_, 1);
v___x_1404_ = l_Lean_instInhabitedExpr;
v___x_1427_ = l_Lean_Expr_binderInfo(v_e_1360_);
v___x_1428_ = l_Lean_BinderInfo_isInstImplicit(v___x_1427_);
if (v___x_1428_ == 0)
{
v___y_1406_ = v___x_1428_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
lean_inc_ref(v_p_1350_);
lean_inc_ref(v_binderType_1402_);
v___x_1429_ = lean_apply_1(v_p_1350_, v_binderType_1402_);
v___x_1430_ = lean_unbox(v___x_1429_);
v___y_1406_ = v___x_1430_;
goto v___jp_1405_;
}
v___jp_1405_:
{
if (v___y_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Meta_mkSorry(v_binderType_1402_, v___y_1406_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v_body_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v_body_1409_ = lean_ctor_get(v_e_1360_, 2);
lean_inc_ref(v_body_1409_);
lean_dec_ref(v_e_1360_);
v___x_1410_ = lean_expr_instantiate1(v_body_1409_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_body_1409_);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_add(v_currentBinderIdx_1352_, v___x_1411_);
lean_dec(v_currentBinderIdx_1352_);
v_e_1351_ = v___x_1410_;
v_currentBinderIdx_1352_ = v___x_1412_;
goto _start;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_e_1360_);
lean_dec_ref(v_currentFVars_1353_);
lean_dec(v_currentBinderIdx_1352_);
lean_dec_ref(v_p_1350_);
v_a_1414_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1407_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1407_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
else
{
lean_object* v___x_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; 
lean_dec_ref(v_binderType_1402_);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___f_1423_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1423_, 0, v___x_1404_);
lean_closure_set(v___f_1423_, 1, v_currentBinderIdx_1352_);
lean_closure_set(v___f_1423_, 2, v___x_1422_);
lean_closure_set(v___f_1423_, 3, v_currentFVars_1353_);
lean_closure_set(v___f_1423_, 4, v_p_1350_);
v___x_1424_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0));
v___x_1425_ = 0;
v___x_1426_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_e_1360_, v___x_1424_, v___f_1423_, v___x_1425_, v___x_1425_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_binderType_1402_);
lean_dec_ref(v_e_1360_);
lean_dec_ref(v_currentFVars_1353_);
lean_dec(v_currentBinderIdx_1352_);
lean_dec_ref(v_p_1350_);
v_a_1431_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1403_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1403_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(lean_object* v___x_1439_, lean_object* v_currentBinderIdx_1440_, lean_object* v___x_1441_, lean_object* v_currentFVars_1442_, lean_object* v_p_1443_, lean_object* v_fvar_1444_, lean_object* v_e_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_array_get_borrowed(v___x_1439_, v_fvar_1444_, v___x_1452_);
v___x_1454_ = l_Lean_Expr_fvarId_x21(v___x_1453_);
v___x_1455_ = lean_nat_add(v_currentBinderIdx_1440_, v___x_1441_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v_currentBinderIdx_1440_);
v___x_1457_ = lean_array_push(v_currentFVars_1442_, v___x_1456_);
v___x_1458_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1443_, v_e_1445_, v___x_1455_, v___x_1457_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___boxed(lean_object* v_p_1459_, lean_object* v_e_1460_, lean_object* v_currentBinderIdx_1461_, lean_object* v_currentFVars_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1459_, v_e_1460_, v_currentBinderIdx_1461_, v_currentFVars_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
return v_res_1469_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(lean_object* v_k_1470_, lean_object* v_t_1471_){
_start:
{
if (lean_obj_tag(v_t_1471_) == 0)
{
lean_object* v_k_1472_; lean_object* v_l_1473_; lean_object* v_r_1474_; uint8_t v___x_1475_; 
v_k_1472_ = lean_ctor_get(v_t_1471_, 1);
v_l_1473_ = lean_ctor_get(v_t_1471_, 3);
v_r_1474_ = lean_ctor_get(v_t_1471_, 4);
v___x_1475_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1470_, v_k_1472_);
switch(v___x_1475_)
{
case 0:
{
v_t_1471_ = v_l_1473_;
goto _start;
}
case 1:
{
uint8_t v___x_1477_; 
v___x_1477_ = 1;
return v___x_1477_;
}
default: 
{
v_t_1471_ = v_r_1474_;
goto _start;
}
}
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = 0;
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg___boxed(lean_object* v_k_1480_, lean_object* v_t_1481_){
_start:
{
uint8_t v_res_1482_; lean_object* v_r_1483_; 
v_res_1482_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_1480_, v_t_1481_);
lean_dec(v_t_1481_);
lean_dec(v_k_1480_);
v_r_1483_ = lean_box(v_res_1482_);
return v_r_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(lean_object* v_val_1484_, lean_object* v_as_1485_, size_t v_i_1486_, size_t v_stop_1487_, lean_object* v_b_1488_){
_start:
{
lean_object* v___y_1490_; uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_eq(v_i_1486_, v_stop_1487_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v_fvarId_1496_; lean_object* v_idx_1497_; uint8_t v___x_1498_; 
v___x_1495_ = lean_array_uget_borrowed(v_as_1485_, v_i_1486_);
v_fvarId_1496_ = lean_ctor_get(v___x_1495_, 0);
v_idx_1497_ = lean_ctor_get(v___x_1495_, 1);
v___x_1498_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_fvarId_1496_, v_val_1484_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_inc(v_idx_1497_);
v___x_1499_ = lean_array_push(v_b_1488_, v_idx_1497_);
v___y_1490_ = v___x_1499_;
goto v___jp_1489_;
}
else
{
v___y_1490_ = v_b_1488_;
goto v___jp_1489_;
}
}
else
{
return v_b_1488_;
}
v___jp_1489_:
{
size_t v___x_1491_; size_t v___x_1492_; 
v___x_1491_ = ((size_t)1ULL);
v___x_1492_ = lean_usize_add(v_i_1486_, v___x_1491_);
v_i_1486_ = v___x_1492_;
v_b_1488_ = v___y_1490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1___boxed(lean_object* v_val_1500_, lean_object* v_as_1501_, lean_object* v_i_1502_, lean_object* v_stop_1503_, lean_object* v_b_1504_){
_start:
{
size_t v_i_boxed_1505_; size_t v_stop_boxed_1506_; lean_object* v_res_1507_; 
v_i_boxed_1505_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_stop_boxed_1506_ = lean_unbox_usize(v_stop_1503_);
lean_dec(v_stop_1503_);
v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1500_, v_as_1501_, v_i_boxed_1505_, v_stop_boxed_1506_, v_b_1504_);
lean_dec_ref(v_as_1501_);
lean_dec(v_val_1500_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(lean_object* v_val_1508_, lean_object* v_as_1509_, lean_object* v_start_1510_, lean_object* v_stop_1511_){
_start:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0));
v___x_1513_ = lean_nat_dec_lt(v_start_1510_, v_stop_1511_);
if (v___x_1513_ == 0)
{
return v___x_1512_;
}
else
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_array_get_size(v_as_1509_);
v___x_1515_ = lean_nat_dec_le(v_stop_1511_, v___x_1514_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_nat_dec_lt(v_start_1510_, v___x_1514_);
if (v___x_1516_ == 0)
{
return v___x_1512_;
}
else
{
size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_usize_of_nat(v_start_1510_);
v___x_1518_ = lean_usize_of_nat(v___x_1514_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1508_, v_as_1509_, v___x_1517_, v___x_1518_, v___x_1512_);
return v___x_1519_;
}
}
else
{
size_t v___x_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_usize_of_nat(v_start_1510_);
v___x_1521_ = lean_usize_of_nat(v_stop_1511_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1508_, v_as_1509_, v___x_1520_, v___x_1521_, v___x_1512_);
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1___boxed(lean_object* v_val_1523_, lean_object* v_as_1524_, lean_object* v_start_1525_, lean_object* v_stop_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v_val_1523_, v_as_1524_, v_start_1525_, v_stop_1526_);
lean_dec(v_stop_1526_);
lean_dec(v_start_1525_);
lean_dec_ref(v_as_1524_);
lean_dec(v_val_1523_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(lean_object* v_p_1530_, lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1537_ = lean_box(1);
v___x_1538_ = lean_st_mk_ref(v___x_1537_);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0));
v___x_1541_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1530_, v_e_1531_, v___x_1539_, v___x_1540_, v___x_1538_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1552_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1552_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1552_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1546_ = lean_st_ref_get(v___x_1538_);
lean_dec(v___x_1538_);
v___x_1547_ = lean_array_get_size(v_a_1542_);
v___x_1548_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v___x_1546_, v_a_1542_, v___x_1539_, v___x_1547_);
lean_dec(v_a_1542_);
lean_dec(v___x_1546_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1548_);
v___x_1550_ = v___x_1544_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v___x_1538_);
v_a_1553_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1541_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1541_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___boxed(lean_object* v_p_1561_, lean_object* v_e_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_1561_, v_e_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
return v_res_1568_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(lean_object* v_00_u03b2_1569_, lean_object* v_k_1570_, lean_object* v_t_1571_){
_start:
{
uint8_t v___x_1572_; 
v___x_1572_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_1570_, v_t_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___boxed(lean_object* v_00_u03b2_1573_, lean_object* v_k_1574_, lean_object* v_t_1575_){
_start:
{
uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_res_1576_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(v_00_u03b2_1573_, v_k_1574_, v_t_1575_);
lean_dec(v_t_1575_);
lean_dec(v_k_1574_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(lean_object* v_k_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v_b_1581_, lean_object* v_c_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___x_1588_; 
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
v___x_1588_ = lean_apply_9(v_k_1578_, v_b_1581_, v_c_1582_, v___y_1579_, v___y_1580_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, lean_box(0));
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed(lean_object* v_k_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v_b_1592_, lean_object* v_c_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(v_k_1589_, v___y_1590_, v___y_1591_, v_b_1592_, v_c_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(lean_object* v_type_1600_, lean_object* v_maxFVars_x3f_1601_, lean_object* v_k_1602_, uint8_t v_cleanupAnnotations_1603_, uint8_t v_whnfType_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___f_1612_; lean_object* v___x_1613_; 
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1612_, 0, v_k_1602_);
lean_closure_set(v___f_1612_, 1, v___y_1605_);
lean_closure_set(v___f_1612_, 2, v___y_1606_);
v___x_1613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1600_, v_maxFVars_x3f_1601_, v___f_1612_, v_cleanupAnnotations_1603_, v_whnfType_1604_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1613_) == 0)
{
return v___x_1613_;
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___boxed(lean_object* v_type_1622_, lean_object* v_maxFVars_x3f_1623_, lean_object* v_k_1624_, lean_object* v_cleanupAnnotations_1625_, lean_object* v_whnfType_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1634_; uint8_t v_whnfType_boxed_1635_; lean_object* v_res_1636_; 
v_cleanupAnnotations_boxed_1634_ = lean_unbox(v_cleanupAnnotations_1625_);
v_whnfType_boxed_1635_ = lean_unbox(v_whnfType_1626_);
v_res_1636_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1622_, v_maxFVars_x3f_1623_, v_k_1624_, v_cleanupAnnotations_boxed_1634_, v_whnfType_boxed_1635_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(lean_object* v_00_u03b1_1637_, lean_object* v_type_1638_, lean_object* v_maxFVars_x3f_1639_, lean_object* v_k_1640_, uint8_t v_cleanupAnnotations_1641_, uint8_t v_whnfType_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1638_, v_maxFVars_x3f_1639_, v_k_1640_, v_cleanupAnnotations_1641_, v_whnfType_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_type_1652_, lean_object* v_maxFVars_x3f_1653_, lean_object* v_k_1654_, lean_object* v_cleanupAnnotations_1655_, lean_object* v_whnfType_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1664_; uint8_t v_whnfType_boxed_1665_; lean_object* v_res_1666_; 
v_cleanupAnnotations_boxed_1664_ = lean_unbox(v_cleanupAnnotations_1655_);
v_whnfType_boxed_1665_ = lean_unbox(v_whnfType_1656_);
v_res_1666_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(v_00_u03b1_1651_, v_type_1652_, v_maxFVars_x3f_1653_, v_k_1654_, v_cleanupAnnotations_boxed_1664_, v_whnfType_boxed_1665_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1666_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(lean_object* v_a_1667_, lean_object* v_as_1668_, size_t v_i_1669_, size_t v_stop_1670_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_usize_dec_eq(v_i_1669_, v_stop_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = lean_array_uget_borrowed(v_as_1668_, v_i_1669_);
v___x_1673_ = lean_nat_dec_eq(v_a_1667_, v___x_1672_);
if (v___x_1673_ == 0)
{
size_t v___x_1674_; size_t v___x_1675_; 
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1669_, v___x_1674_);
v_i_1669_ = v___x_1675_;
goto _start;
}
else
{
return v___x_1673_;
}
}
else
{
uint8_t v___x_1677_; 
v___x_1677_ = 0;
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0___boxed(lean_object* v_a_1678_, lean_object* v_as_1679_, lean_object* v_i_1680_, lean_object* v_stop_1681_){
_start:
{
size_t v_i_boxed_1682_; size_t v_stop_boxed_1683_; uint8_t v_res_1684_; lean_object* v_r_1685_; 
v_i_boxed_1682_ = lean_unbox_usize(v_i_1680_);
lean_dec(v_i_1680_);
v_stop_boxed_1683_ = lean_unbox_usize(v_stop_1681_);
lean_dec(v_stop_1681_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_1678_, v_as_1679_, v_i_boxed_1682_, v_stop_boxed_1683_);
lean_dec_ref(v_as_1679_);
lean_dec(v_a_1678_);
v_r_1685_ = lean_box(v_res_1684_);
return v_r_1685_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(lean_object* v_as_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = lean_array_get_size(v_as_1686_);
v___x_1690_ = lean_nat_dec_lt(v___x_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
return v___x_1690_;
}
else
{
if (v___x_1690_ == 0)
{
return v___x_1690_;
}
else
{
size_t v___x_1691_; size_t v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = ((size_t)0ULL);
v___x_1692_ = lean_usize_of_nat(v___x_1689_);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_1687_, v_as_1686_, v___x_1691_, v___x_1692_);
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0___boxed(lean_object* v_as_1694_, lean_object* v_a_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v_as_1694_, v_a_1695_);
lean_dec(v_a_1695_);
lean_dec_ref(v_as_1694_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(lean_object* v___x_1698_, lean_object* v___x_1699_, lean_object* v___x_1700_, uint8_t v___x_1701_, lean_object* v_fvars_1702_, size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_bs_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_bs_1705_);
return v___x_1712_;
}
else
{
uint8_t v___x_1713_; lean_object* v_v_1714_; lean_object* v___x_1715_; lean_object* v_bs_x27_1716_; lean_object* v___y_1718_; lean_object* v___y_1719_; uint8_t v___y_1720_; lean_object* v___y_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1713_ = lean_nat_dec_lt(v___x_1699_, v___x_1700_);
v_v_1714_ = lean_array_uget(v_bs_1705_, v_i_1704_);
v___x_1715_ = lean_unsigned_to_nat(0u);
v_bs_x27_1716_ = lean_array_uset(v_bs_1705_, v_i_1704_, v___x_1715_);
v___x_1730_ = lean_array_get_size(v_fvars_1702_);
v___x_1731_ = lean_nat_dec_lt(v_v_1714_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_box(0);
v___y_1727_ = v___x_1732_;
v_a_1728_ = v___x_1732_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = lean_array_fget_borrowed(v_fvars_1702_, v_v_1714_);
lean_inc_n(v___x_1733_, 2);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
v___x_1735_ = lean_infer_type(v___x_1733_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_a_1736_);
v___y_1727_ = v___x_1734_;
v_a_1728_ = v___x_1737_;
goto v___jp_1726_;
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref_known(v___x_1734_, 1);
lean_dec_ref(v_bs_x27_1716_);
lean_dec(v_v_1714_);
v_a_1738_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1735_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1735_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
v___jp_1717_:
{
lean_object* v___x_1721_; size_t v___x_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1721_, 0, v___y_1719_);
lean_ctor_set(v___x_1721_, 1, v___y_1718_);
lean_ctor_set(v___x_1721_, 2, v_v_1714_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*3, v___y_1720_);
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1704_, v___x_1722_);
v___x_1724_ = lean_array_uset(v_bs_x27_1716_, v_i_1704_, v___x_1721_);
v_i_1704_ = v___x_1723_;
v_bs_1705_ = v___x_1724_;
goto _start;
}
v___jp_1726_:
{
uint8_t v___x_1729_; 
v___x_1729_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v___x_1698_, v_v_1714_);
if (v___x_1729_ == 0)
{
v___y_1718_ = v_a_1728_;
v___y_1719_ = v___y_1727_;
v___y_1720_ = v___x_1713_;
goto v___jp_1717_;
}
else
{
v___y_1718_ = v_a_1728_;
v___y_1719_ = v___y_1727_;
v___y_1720_ = v___x_1701_;
goto v___jp_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg___boxed(lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v___x_1748_, lean_object* v___x_1749_, lean_object* v_fvars_1750_, lean_object* v_sz_1751_, lean_object* v_i_1752_, lean_object* v_bs_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v___x_3282__boxed_1759_; size_t v_sz_boxed_1760_; size_t v_i_boxed_1761_; lean_object* v_res_1762_; 
v___x_3282__boxed_1759_ = lean_unbox(v___x_1749_);
v_sz_boxed_1760_ = lean_unbox_usize(v_sz_1751_);
lean_dec(v_sz_1751_);
v_i_boxed_1761_ = lean_unbox_usize(v_i_1752_);
lean_dec(v_i_1752_);
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1746_, v___x_1747_, v___x_1748_, v___x_3282__boxed_1759_, v_fvars_1750_, v_sz_boxed_1760_, v_i_boxed_1761_, v_bs_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v_fvars_1750_);
lean_dec(v___x_1748_);
lean_dec(v___x_1747_);
lean_dec_ref(v___x_1746_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(lean_object* v_p_1763_, lean_object* v_type_1764_, lean_object* v_a_1765_, lean_object* v___x_1766_, lean_object* v___x_1767_, uint8_t v___x_1768_, lean_object* v_logOnUnused_1769_, lean_object* v_fvars_1770_, lean_object* v_x_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; size_t v_sz_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1779_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(v_p_1763_, v_type_1764_);
v_sz_1780_ = lean_array_size(v_a_1765_);
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1779_, v___x_1766_, v___x_1767_, v___x_1768_, v_fvars_1770_, v_sz_1780_, v___x_1781_, v_a_1765_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec_ref(v___x_1779_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
lean_inc(v___y_1777_);
lean_inc_ref(v___y_1776_);
lean_inc(v___y_1775_);
lean_inc_ref(v___y_1774_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
v___x_1784_ = lean_apply_8(v_logOnUnused_1769_, v_a_1783_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, lean_box(0));
return v___x_1784_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v_logOnUnused_1769_);
v_a_1785_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1782_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1782_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed(lean_object* v_p_1793_, lean_object* v_type_1794_, lean_object* v_a_1795_, lean_object* v___x_1796_, lean_object* v___x_1797_, lean_object* v___x_1798_, lean_object* v_logOnUnused_1799_, lean_object* v_fvars_1800_, lean_object* v_x_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v___x_3375__boxed_1809_; lean_object* v_res_1810_; 
v___x_3375__boxed_1809_ = lean_unbox(v___x_1798_);
v_res_1810_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(v_p_1793_, v_type_1794_, v_a_1795_, v___x_1796_, v___x_1797_, v___x_3375__boxed_1809_, v_logOnUnused_1799_, v_fvars_1800_, v_x_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec_ref(v_x_1801_);
lean_dec_ref(v_fvars_1800_);
lean_dec(v___x_1797_);
lean_dec(v___x_1796_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(lean_object* v_decl_1811_, lean_object* v_p_1812_, lean_object* v_logOnUnused_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_type_1821_; lean_object* v___x_1822_; 
v_type_1821_ = lean_ctor_get(v_decl_1811_, 2);
lean_inc_ref_n(v_type_1821_, 2);
lean_dec_ref(v_decl_1811_);
lean_inc_ref(v_p_1812_);
v___x_1822_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_1812_, v_type_1821_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1846_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1846_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1846_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1827_ = lean_array_get_size(v_a_1823_);
v___x_1828_ = lean_unsigned_to_nat(1u);
v___x_1829_ = lean_nat_sub(v___x_1827_, v___x_1828_);
v___x_1830_ = lean_nat_dec_lt(v___x_1829_, v___x_1827_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
lean_dec(v___x_1829_);
lean_dec(v_a_1823_);
lean_dec_ref(v_type_1821_);
lean_dec_ref(v_logOnUnused_1813_);
lean_dec_ref(v_p_1812_);
v___x_1831_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1831_);
v___x_1833_ = v___x_1825_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Expr_hasSorry(v_type_1821_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_del_object(v___x_1825_);
v___x_1836_ = lean_box(v___x_1835_);
lean_inc(v___x_1829_);
lean_inc(v_a_1823_);
lean_inc_ref(v_type_1821_);
v___f_1837_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1837_, 0, v_p_1812_);
lean_closure_set(v___f_1837_, 1, v_type_1821_);
lean_closure_set(v___f_1837_, 2, v_a_1823_);
lean_closure_set(v___f_1837_, 3, v___x_1829_);
lean_closure_set(v___f_1837_, 4, v___x_1827_);
lean_closure_set(v___f_1837_, 5, v___x_1836_);
lean_closure_set(v___f_1837_, 6, v_logOnUnused_1813_);
v___x_1838_ = lean_array_fget(v_a_1823_, v___x_1829_);
lean_dec(v___x_1829_);
lean_dec(v_a_1823_);
v___x_1839_ = lean_nat_add(v___x_1838_, v___x_1828_);
lean_dec(v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
v___x_1841_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1821_, v___x_1840_, v___f_1837_, v___x_1830_, v___x_1835_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
lean_dec(v___x_1829_);
lean_dec(v_a_1823_);
lean_dec_ref(v_type_1821_);
lean_dec_ref(v_logOnUnused_1813_);
lean_dec_ref(v_p_1812_);
v___x_1842_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1842_);
v___x_1844_ = v___x_1825_;
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
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_type_1821_);
lean_dec_ref(v_logOnUnused_1813_);
lean_dec_ref(v_p_1812_);
v_a_1847_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1822_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1822_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___boxed(lean_object* v_decl_1855_, lean_object* v_p_1856_, lean_object* v_logOnUnused_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_decl_1855_, v_p_1856_, v_logOnUnused_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, uint8_t v___x_1869_, lean_object* v_fvars_1870_, size_t v_sz_1871_, size_t v_i_1872_, lean_object* v_bs_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1866_, v___x_1867_, v___x_1868_, v___x_1869_, v_fvars_1870_, v_sz_1871_, v_i_1872_, v_bs_1873_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___boxed(lean_object* v___x_1882_, lean_object* v___x_1883_, lean_object* v___x_1884_, lean_object* v___x_1885_, lean_object* v_fvars_1886_, lean_object* v_sz_1887_, lean_object* v_i_1888_, lean_object* v_bs_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
uint8_t v___x_3506__boxed_1897_; size_t v_sz_boxed_1898_; size_t v_i_boxed_1899_; lean_object* v_res_1900_; 
v___x_3506__boxed_1897_ = lean_unbox(v___x_1885_);
v_sz_boxed_1898_ = lean_unbox_usize(v_sz_1887_);
lean_dec(v_sz_1887_);
v_i_boxed_1899_ = lean_unbox_usize(v_i_1888_);
lean_dec(v_i_1888_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(v___x_1882_, v___x_1883_, v___x_1884_, v___x_3506__boxed_1897_, v_fvars_1886_, v_sz_boxed_1898_, v_i_boxed_1899_, v_bs_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v_fvars_1886_);
lean_dec(v___x_1884_);
lean_dec(v___x_1883_);
lean_dec_ref(v___x_1882_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(lean_object* v_env_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
if (lean_obj_tag(v_a_1902_) == 0)
{
lean_object* v___x_1904_; 
lean_dec_ref(v_env_1901_);
v___x_1904_ = lean_array_to_list(v_a_1903_);
return v___x_1904_;
}
else
{
lean_object* v_head_1905_; lean_object* v_tail_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; 
v_head_1905_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_head_1905_);
v_tail_1906_ = lean_ctor_get(v_a_1902_, 1);
lean_inc(v_tail_1906_);
lean_dec_ref_known(v_a_1902_, 2);
v___x_1907_ = 0;
lean_inc_ref(v_env_1901_);
v___x_1908_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_1901_, v_head_1905_, v___x_1907_);
if (lean_obj_tag(v___x_1908_) == 0)
{
v_a_1902_ = v_tail_1906_;
goto _start;
}
else
{
lean_object* v_val_1910_; lean_object* v___x_1911_; 
v_val_1910_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_val_1910_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1911_ = lean_array_push(v_a_1903_, v_val_1910_);
v_a_1902_ = v_tail_1906_;
v_a_1903_ = v___x_1911_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(lean_object* v_t_1915_, lean_object* v_env_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = l_Lean_Linter_getDeclsByBody(v_t_1915_);
v___x_1918_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0));
v___x_1919_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(v_env_1916_, v___x_1917_, v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(lean_object* v_n_1938_){
_start:
{
uint8_t v___y_1940_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9));
v___x_1950_ = lean_name_eq(v_n_1938_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1951_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11));
v___x_1952_ = lean_name_eq(v_n_1938_, v___x_1951_);
v___y_1940_ = v___x_1952_;
goto v___jp_1939_;
}
else
{
v___y_1940_ = v___x_1950_;
goto v___jp_1939_;
}
v___jp_1939_:
{
if (v___y_1940_ == 0)
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1));
v___x_1942_ = lean_name_eq(v_n_1938_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3));
v___x_1944_ = lean_name_eq(v_n_1938_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5));
v___x_1946_ = lean_name_eq(v_n_1938_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7));
v___x_1948_ = lean_name_eq(v_n_1938_, v___x_1947_);
return v___x_1948_;
}
else
{
return v___x_1946_;
}
}
else
{
return v___x_1944_;
}
}
else
{
return v___x_1942_;
}
}
else
{
return v___y_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___boxed(lean_object* v_n_1953_){
_start:
{
uint8_t v_res_1954_; lean_object* v_r_1955_; 
v_res_1954_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(v_n_1953_);
lean_dec(v_n_1953_);
v_r_1955_ = lean_box(v_res_1954_);
return v_r_1955_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(lean_object* v_type_1957_){
_start:
{
lean_object* v___f_1958_; uint8_t v___x_1959_; 
v___f_1958_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0));
v___x_1959_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(v___f_1958_, v_type_1957_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___boxed(lean_object* v_type_1960_){
_start:
{
uint8_t v_res_1961_; lean_object* v_r_1962_; 
v_res_1961_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(v_type_1960_);
v_r_1962_ = lean_box(v_res_1961_);
return v_r_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v_infoState_1966_; lean_object* v_trees_1967_; lean_object* v___x_1968_; 
v___x_1965_ = lean_st_ref_get(v___y_1963_);
v_infoState_1966_ = lean_ctor_get(v___x_1965_, 8);
lean_inc_ref(v_infoState_1966_);
lean_dec(v___x_1965_);
v_trees_1967_ = lean_ctor_get(v_infoState_1966_, 2);
lean_inc_ref(v_trees_1967_);
lean_dec_ref(v_infoState_1966_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v_trees_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg___boxed(lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_1969_);
lean_dec(v___y_1969_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___boxed(lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(uint8_t v___x_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
if (lean_obj_tag(v_a_1982_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_List_reverse___redArg(v_a_1983_);
return v___x_1984_;
}
else
{
lean_object* v_head_1985_; lean_object* v_tail_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2004_; 
v_head_1985_ = lean_ctor_get(v_a_1982_, 0);
v_tail_1986_ = lean_ctor_get(v_a_1982_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_a_1982_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1988_ = v_a_1982_;
v_isShared_1989_ = v_isSharedCheck_2004_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_tail_1986_);
lean_inc(v_head_1985_);
lean_dec(v_a_1982_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2004_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_name_1990_; lean_object* v_type_1991_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_name_1990_ = lean_ctor_get(v_head_1985_, 0);
v_type_1991_ = lean_ctor_get(v_head_1985_, 2);
v___x_2000_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9));
lean_inc(v_name_1990_);
v___x_2001_ = l_Lean_privateToUserName(v_name_1990_);
v___x_2002_ = l_Lean_Name_isPrefixOf(v___x_2000_, v___x_2001_);
lean_dec(v___x_2001_);
if (v___x_2002_ == 0)
{
goto v___jp_1992_;
}
else
{
if (v___x_1981_ == 0)
{
lean_del_object(v___x_1988_);
lean_dec(v_head_1985_);
v_a_1982_ = v_tail_1986_;
goto _start;
}
else
{
goto v___jp_1992_;
}
}
v___jp_1992_:
{
lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0));
lean_inc_ref(v_type_1991_);
v___x_1994_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(v___x_1993_, v_type_1991_);
if (v___x_1994_ == 0)
{
lean_del_object(v___x_1988_);
lean_dec(v_head_1985_);
v_a_1982_ = v_tail_1986_;
goto _start;
}
else
{
lean_object* v___x_1997_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v_a_1983_);
v___x_1997_ = v___x_1988_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_head_1985_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_a_1983_);
v___x_1997_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
v_a_1982_ = v_tail_1986_;
v_a_1983_ = v___x_1997_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___boxed(lean_object* v___x_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
uint8_t v___x_11443__boxed_2008_; lean_object* v_res_2009_; 
v___x_11443__boxed_2008_ = lean_unbox(v___x_2005_);
v_res_2009_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_11443__boxed_2008_, v_a_2006_, v_a_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(lean_object* v_o_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v_env_2014_; lean_object* v___x_2015_; lean_object* v_toEnvExtension_2016_; lean_object* v_asyncMode_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_merged_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2029_; 
v___x_2013_ = lean_st_ref_get(v___y_2011_);
v_env_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_env_2014_);
lean_dec(v___x_2013_);
v___x_2015_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2016_ = lean_ctor_get(v___x_2015_, 0);
v_asyncMode_2017_ = lean_ctor_get(v_toEnvExtension_2016_, 2);
v___x_2018_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2019_ = lean_box(0);
v___x_2020_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2018_, v___x_2015_, v_env_2014_, v_asyncMode_2017_, v___x_2019_);
v_merged_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_2020_, 1);
lean_dec(v_unused_2030_);
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_merged_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v_merged_2021_);
lean_ctor_set(v___x_2023_, 0, v_o_2010_);
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_o_2010_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_merged_2021_);
v___x_2026_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_o_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_o_2031_, v___y_2032_);
lean_dec(v___y_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_toCold_2042_; lean_object* v_options_2043_; lean_object* v___x_2044_; 
v_toCold_2042_ = lean_ctor_get(v___y_2039_, 0);
v_options_2043_ = lean_ctor_get(v_toCold_2042_, 2);
lean_inc_ref(v_options_2043_);
v___x_2044_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_options_2043_, v___y_2040_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3___boxed(lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(lean_object* v_msgData_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v_env_2060_; lean_object* v___x_2061_; lean_object* v_toCold_2062_; lean_object* v_mctx_2063_; lean_object* v_lctx_2064_; lean_object* v_options_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2059_ = lean_st_ref_get(v___y_2057_);
v_env_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc_ref(v_env_2060_);
lean_dec(v___x_2059_);
v___x_2061_ = lean_st_ref_get(v___y_2055_);
v_toCold_2062_ = lean_ctor_get(v___y_2056_, 0);
v_mctx_2063_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref(v_mctx_2063_);
lean_dec(v___x_2061_);
v_lctx_2064_ = lean_ctor_get(v___y_2054_, 2);
v_options_2065_ = lean_ctor_get(v_toCold_2062_, 2);
lean_inc_ref(v_options_2065_);
lean_inc_ref(v_lctx_2064_);
v___x_2066_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2066_, 0, v_env_2060_);
lean_ctor_set(v___x_2066_, 1, v_mctx_2063_);
lean_ctor_set(v___x_2066_, 2, v_lctx_2064_);
lean_ctor_set(v___x_2066_, 3, v_options_2065_);
v___x_2067_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v_msgData_2053_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13___boxed(lean_object* v_msgData_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(v_msgData_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(lean_object* v_opts_2076_, lean_object* v_opt_2077_){
_start:
{
lean_object* v_name_2078_; lean_object* v_defValue_2079_; lean_object* v_map_2080_; lean_object* v___x_2081_; 
v_name_2078_ = lean_ctor_get(v_opt_2077_, 0);
v_defValue_2079_ = lean_ctor_get(v_opt_2077_, 1);
v_map_2080_ = lean_ctor_get(v_opts_2076_, 0);
v___x_2081_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2080_, v_name_2078_);
if (lean_obj_tag(v___x_2081_) == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_unbox(v_defValue_2079_);
return v___x_2082_;
}
else
{
lean_object* v_val_2083_; 
v_val_2083_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v___x_2081_, 1);
if (lean_obj_tag(v_val_2083_) == 1)
{
uint8_t v_v_2084_; 
v_v_2084_ = lean_ctor_get_uint8(v_val_2083_, 0);
lean_dec_ref_known(v_val_2083_, 0);
return v_v_2084_;
}
else
{
uint8_t v___x_2085_; 
lean_dec(v_val_2083_);
v___x_2085_ = lean_unbox(v_defValue_2079_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14___boxed(lean_object* v_opts_2086_, lean_object* v_opt_2087_){
_start:
{
uint8_t v_res_2088_; lean_object* v_r_2089_; 
v_res_2088_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(v_opts_2086_, v_opt_2087_);
lean_dec_ref(v_opt_2087_);
lean_dec_ref(v_opts_2086_);
v_r_2089_ = lean_box(v_res_2088_);
return v_r_2089_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(uint8_t v_suppressElabErrors_2098_, uint8_t v___y_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 1)
{
lean_object* v_pre_2101_; 
v_pre_2101_ = lean_ctor_get(v_x_2100_, 0);
switch(lean_obj_tag(v_pre_2101_))
{
case 1:
{
lean_object* v_pre_2102_; 
v_pre_2102_ = lean_ctor_get(v_pre_2101_, 0);
switch(lean_obj_tag(v_pre_2102_))
{
case 0:
{
lean_object* v_str_2103_; lean_object* v_str_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_str_2103_ = lean_ctor_get(v_x_2100_, 1);
v_str_2104_ = lean_ctor_get(v_pre_2101_, 1);
v___x_2105_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__0));
v___x_2106_ = lean_string_dec_eq(v_str_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__1));
v___x_2108_ = lean_string_dec_eq(v_str_2104_, v___x_2107_);
if (v___x_2108_ == 0)
{
return v___x_2108_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__2));
v___x_2110_ = lean_string_dec_eq(v_str_2103_, v___x_2109_);
if (v___x_2110_ == 0)
{
return v___x_2110_;
}
else
{
return v_suppressElabErrors_2098_;
}
}
}
else
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__3));
v___x_2112_ = lean_string_dec_eq(v_str_2103_, v___x_2111_);
if (v___x_2112_ == 0)
{
return v___x_2112_;
}
else
{
return v_suppressElabErrors_2098_;
}
}
}
case 1:
{
lean_object* v_pre_2113_; 
v_pre_2113_ = lean_ctor_get(v_pre_2102_, 0);
if (lean_obj_tag(v_pre_2113_) == 0)
{
lean_object* v_str_2114_; lean_object* v_str_2115_; lean_object* v_str_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v_str_2114_ = lean_ctor_get(v_x_2100_, 1);
v_str_2115_ = lean_ctor_get(v_pre_2101_, 1);
v_str_2116_ = lean_ctor_get(v_pre_2102_, 1);
v___x_2117_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__4));
v___x_2118_ = lean_string_dec_eq(v_str_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__5));
v___x_2120_ = lean_string_dec_eq(v_str_2115_, v___x_2119_);
if (v___x_2120_ == 0)
{
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__6));
v___x_2122_ = lean_string_dec_eq(v_str_2114_, v___x_2121_);
if (v___x_2122_ == 0)
{
return v___x_2122_;
}
else
{
return v_suppressElabErrors_2098_;
}
}
}
}
else
{
return v___y_2099_;
}
}
default: 
{
return v___y_2099_;
}
}
}
case 0:
{
lean_object* v_str_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_str_2123_ = lean_ctor_get(v_x_2100_, 1);
v___x_2124_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__7));
v___x_2125_ = lean_string_dec_eq(v_str_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
return v___x_2125_;
}
else
{
return v_suppressElabErrors_2098_;
}
}
default: 
{
return v___y_2099_;
}
}
}
else
{
return v___y_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2126_, lean_object* v___y_2127_, lean_object* v_x_2128_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2129_; uint8_t v___y_11599__boxed_2130_; uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_suppressElabErrors_boxed_2129_ = lean_unbox(v_suppressElabErrors_2126_);
v___y_11599__boxed_2130_ = lean_unbox(v___y_2127_);
v_res_2131_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(v_suppressElabErrors_boxed_2129_, v___y_11599__boxed_2130_, v_x_2128_);
lean_dec(v_x_2128_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_ref_2133_, lean_object* v_msgData_2134_, uint8_t v_severity_2135_, uint8_t v_isSilent_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; uint8_t v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; uint8_t v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2180_; lean_object* v___y_2181_; uint8_t v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; uint8_t v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2205_; lean_object* v___y_2206_; uint8_t v___y_2207_; uint8_t v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2216_; lean_object* v___y_2217_; uint8_t v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; uint8_t v___y_2221_; uint8_t v___y_2222_; uint8_t v___x_2227_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; uint8_t v___y_2233_; uint8_t v___y_2234_; uint8_t v___y_2235_; uint8_t v___y_2237_; uint8_t v___x_2253_; 
v___x_2227_ = 2;
v___x_2253_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2135_, v___x_2227_);
if (v___x_2253_ == 0)
{
v___y_2237_ = v___x_2253_;
goto v___jp_2236_;
}
else
{
uint8_t v___x_2254_; 
lean_inc_ref(v_msgData_2134_);
v___x_2254_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2134_);
v___y_2237_ = v___x_2254_;
goto v___jp_2236_;
}
v___jp_2142_:
{
lean_object* v___x_2152_; lean_object* v_toCold_2153_; lean_object* v_currNamespace_2154_; lean_object* v_openDecls_2155_; lean_object* v_env_2156_; lean_object* v_nextMacroScope_2157_; lean_object* v_ngen_2158_; lean_object* v_auxDeclNGen_2159_; lean_object* v_traceState_2160_; lean_object* v_cache_2161_; lean_object* v_messages_2162_; lean_object* v_infoState_2163_; lean_object* v_snapshotTasks_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2178_; 
v___x_2152_ = lean_st_ref_take(v___y_2151_);
v_toCold_2153_ = lean_ctor_get(v___y_2150_, 0);
v_currNamespace_2154_ = lean_ctor_get(v_toCold_2153_, 4);
v_openDecls_2155_ = lean_ctor_get(v_toCold_2153_, 5);
v_env_2156_ = lean_ctor_get(v___x_2152_, 0);
v_nextMacroScope_2157_ = lean_ctor_get(v___x_2152_, 1);
v_ngen_2158_ = lean_ctor_get(v___x_2152_, 2);
v_auxDeclNGen_2159_ = lean_ctor_get(v___x_2152_, 3);
v_traceState_2160_ = lean_ctor_get(v___x_2152_, 4);
v_cache_2161_ = lean_ctor_get(v___x_2152_, 5);
v_messages_2162_ = lean_ctor_get(v___x_2152_, 6);
v_infoState_2163_ = lean_ctor_get(v___x_2152_, 7);
v_snapshotTasks_2164_ = lean_ctor_get(v___x_2152_, 8);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2166_ = v___x_2152_;
v_isShared_2167_ = v_isSharedCheck_2178_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_snapshotTasks_2164_);
lean_inc(v_infoState_2163_);
lean_inc(v_messages_2162_);
lean_inc(v_cache_2161_);
lean_inc(v_traceState_2160_);
lean_inc(v_auxDeclNGen_2159_);
lean_inc(v_ngen_2158_);
lean_inc(v_nextMacroScope_2157_);
lean_inc(v_env_2156_);
lean_dec(v___x_2152_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2178_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_inc(v_openDecls_2155_);
lean_inc(v_currNamespace_2154_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_currNamespace_2154_);
lean_ctor_set(v___x_2168_, 1, v_openDecls_2155_);
v___x_2169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___y_2144_);
lean_inc_ref(v___y_2145_);
lean_inc_ref(v___y_2148_);
v___x_2170_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2170_, 0, v___y_2148_);
lean_ctor_set(v___x_2170_, 1, v___y_2147_);
lean_ctor_set(v___x_2170_, 2, v___y_2143_);
lean_ctor_set(v___x_2170_, 3, v___y_2145_);
lean_ctor_set(v___x_2170_, 4, v___x_2169_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*5, v___y_2149_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*5 + 1, v___y_2146_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*5 + 2, v_isSilent_2136_);
v___x_2171_ = l_Lean_MessageLog_add(v___x_2170_, v_messages_2162_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 6, v___x_2171_);
v___x_2173_ = v___x_2166_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_env_2156_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_nextMacroScope_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_ngen_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_auxDeclNGen_2159_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_traceState_2160_);
lean_ctor_set(v_reuseFailAlloc_2177_, 5, v_cache_2161_);
lean_ctor_set(v_reuseFailAlloc_2177_, 6, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2177_, 7, v_infoState_2163_);
lean_ctor_set(v_reuseFailAlloc_2177_, 8, v_snapshotTasks_2164_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_st_ref_put(v___y_2151_, v___x_2173_);
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
}
}
v___jp_2179_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2203_; 
v___x_2188_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2134_);
v___x_2189_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(v___x_2188_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2203_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_inc_ref_n(v___y_2185_, 2);
v___x_2194_ = l_Lean_FileMap_toPosition(v___y_2185_, v___y_2181_);
lean_dec(v___y_2181_);
v___x_2195_ = l_Lean_FileMap_toPosition(v___y_2185_, v___y_2187_);
lean_dec(v___y_2187_);
v___x_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
v___x_2197_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4));
if (v___y_2182_ == 0)
{
lean_del_object(v___x_2192_);
lean_dec_ref(v___y_2180_);
v___y_2143_ = v___x_2196_;
v___y_2144_ = v_a_2190_;
v___y_2145_ = v___x_2197_;
v___y_2146_ = v___y_2183_;
v___y_2147_ = v___x_2194_;
v___y_2148_ = v___y_2184_;
v___y_2149_ = v___y_2186_;
v___y_2150_ = v___y_2139_;
v___y_2151_ = v___y_2140_;
goto v___jp_2142_;
}
else
{
uint8_t v___x_2198_; 
lean_inc(v_a_2190_);
v___x_2198_ = l_Lean_MessageData_hasTag(v___y_2180_, v_a_2190_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_dec_ref_known(v___x_2196_, 1);
lean_dec_ref(v___x_2194_);
lean_dec(v_a_2190_);
v___x_2199_ = lean_box(0);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2199_);
v___x_2201_ = v___x_2192_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
else
{
lean_del_object(v___x_2192_);
v___y_2143_ = v___x_2196_;
v___y_2144_ = v_a_2190_;
v___y_2145_ = v___x_2197_;
v___y_2146_ = v___y_2183_;
v___y_2147_ = v___x_2194_;
v___y_2148_ = v___y_2184_;
v___y_2149_ = v___y_2186_;
v___y_2150_ = v___y_2139_;
v___y_2151_ = v___y_2140_;
goto v___jp_2142_;
}
}
}
}
v___jp_2204_:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Syntax_getTailPos_x3f(v___y_2206_, v___y_2211_);
lean_dec(v___y_2206_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_inc(v___y_2212_);
v___y_2180_ = v___y_2205_;
v___y_2181_ = v___y_2212_;
v___y_2182_ = v___y_2207_;
v___y_2183_ = v___y_2208_;
v___y_2184_ = v___y_2210_;
v___y_2185_ = v___y_2209_;
v___y_2186_ = v___y_2211_;
v___y_2187_ = v___y_2212_;
goto v___jp_2179_;
}
else
{
lean_object* v_val_2214_; 
v_val_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___y_2180_ = v___y_2205_;
v___y_2181_ = v___y_2212_;
v___y_2182_ = v___y_2207_;
v___y_2183_ = v___y_2208_;
v___y_2184_ = v___y_2210_;
v___y_2185_ = v___y_2209_;
v___y_2186_ = v___y_2211_;
v___y_2187_ = v_val_2214_;
goto v___jp_2179_;
}
}
v___jp_2215_:
{
lean_object* v_ref_2223_; lean_object* v___x_2224_; 
v_ref_2223_ = l_Lean_replaceRef(v_ref_2133_, v___y_2217_);
v___x_2224_ = l_Lean_Syntax_getPos_x3f(v_ref_2223_, v___y_2221_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_unsigned_to_nat(0u);
v___y_2205_ = v___y_2216_;
v___y_2206_ = v_ref_2223_;
v___y_2207_ = v___y_2218_;
v___y_2208_ = v___y_2222_;
v___y_2209_ = v___y_2220_;
v___y_2210_ = v___y_2219_;
v___y_2211_ = v___y_2221_;
v___y_2212_ = v___x_2225_;
goto v___jp_2204_;
}
else
{
lean_object* v_val_2226_; 
v_val_2226_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_val_2226_);
lean_dec_ref_known(v___x_2224_, 1);
v___y_2205_ = v___y_2216_;
v___y_2206_ = v_ref_2223_;
v___y_2207_ = v___y_2218_;
v___y_2208_ = v___y_2222_;
v___y_2209_ = v___y_2220_;
v___y_2210_ = v___y_2219_;
v___y_2211_ = v___y_2221_;
v___y_2212_ = v_val_2226_;
goto v___jp_2204_;
}
}
v___jp_2228_:
{
if (v___y_2235_ == 0)
{
v___y_2216_ = v___y_2229_;
v___y_2217_ = v___y_2232_;
v___y_2218_ = v___y_2233_;
v___y_2219_ = v___y_2231_;
v___y_2220_ = v___y_2230_;
v___y_2221_ = v___y_2234_;
v___y_2222_ = v_severity_2135_;
goto v___jp_2215_;
}
else
{
v___y_2216_ = v___y_2229_;
v___y_2217_ = v___y_2232_;
v___y_2218_ = v___y_2233_;
v___y_2219_ = v___y_2231_;
v___y_2220_ = v___y_2230_;
v___y_2221_ = v___y_2234_;
v___y_2222_ = v___x_2227_;
goto v___jp_2215_;
}
}
v___jp_2236_:
{
if (v___y_2237_ == 0)
{
lean_object* v_toCold_2238_; lean_object* v_ref_2239_; uint8_t v_suppressElabErrors_2240_; lean_object* v_fileName_2241_; lean_object* v_fileMap_2242_; lean_object* v_options_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; uint8_t v___x_2247_; uint8_t v___x_2248_; 
v_toCold_2238_ = lean_ctor_get(v___y_2139_, 0);
v_ref_2239_ = lean_ctor_get(v___y_2139_, 2);
v_suppressElabErrors_2240_ = lean_ctor_get_uint8(v___y_2139_, sizeof(void*)*3 + 1);
v_fileName_2241_ = lean_ctor_get(v_toCold_2238_, 0);
v_fileMap_2242_ = lean_ctor_get(v_toCold_2238_, 1);
v_options_2243_ = lean_ctor_get(v_toCold_2238_, 2);
v___x_2244_ = lean_box(v_suppressElabErrors_2240_);
v___x_2245_ = lean_box(v___y_2237_);
v___f_2246_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2246_, 0, v___x_2244_);
lean_closure_set(v___f_2246_, 1, v___x_2245_);
v___x_2247_ = 1;
v___x_2248_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2135_, v___x_2247_);
if (v___x_2248_ == 0)
{
v___y_2229_ = v___f_2246_;
v___y_2230_ = v_fileMap_2242_;
v___y_2231_ = v_fileName_2241_;
v___y_2232_ = v_ref_2239_;
v___y_2233_ = v_suppressElabErrors_2240_;
v___y_2234_ = v___y_2237_;
v___y_2235_ = v___x_2248_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = l_Lean_warningAsError;
v___x_2250_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(v_options_2243_, v___x_2249_);
v___y_2229_ = v___f_2246_;
v___y_2230_ = v_fileMap_2242_;
v___y_2231_ = v_fileName_2241_;
v___y_2232_ = v_ref_2239_;
v___y_2233_ = v_suppressElabErrors_2240_;
v___y_2234_ = v___y_2237_;
v___y_2235_ = v___x_2250_;
goto v___jp_2228_;
}
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref(v_msgData_2134_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
return v___x_2252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_ref_2255_, lean_object* v_msgData_2256_, lean_object* v_severity_2257_, lean_object* v_isSilent_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v_severity_boxed_2264_; uint8_t v_isSilent_boxed_2265_; lean_object* v_res_2266_; 
v_severity_boxed_2264_ = lean_unbox(v_severity_2257_);
v_isSilent_boxed_2265_ = lean_unbox(v_isSilent_2258_);
v_res_2266_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2255_, v_msgData_2256_, v_severity_boxed_2264_, v_isSilent_boxed_2265_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v_ref_2255_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(lean_object* v_ref_2267_, lean_object* v_msgData_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v___x_2276_; uint8_t v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = 1;
v___x_2277_ = 0;
v___x_2278_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2267_, v_msgData_2268_, v___x_2276_, v___x_2277_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6___boxed(lean_object* v_ref_2279_, lean_object* v_msgData_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(v_ref_2279_, v_msgData_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v_ref_2279_);
return v_res_2288_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__0));
v___x_2291_ = l_Lean_stringToMessageData(v___x_2290_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__2));
v___x_2294_ = l_Lean_stringToMessageData(v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(lean_object* v_linterOption_2295_, lean_object* v_stx_2296_, lean_object* v_msg_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_name_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2323_; 
v_name_2305_ = lean_ctor_get(v_linterOption_2295_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_linterOption_2295_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v_linterOption_2295_, 1);
lean_dec(v_unused_2324_);
v___x_2307_ = v_linterOption_2295_;
v_isShared_2308_ = v_isSharedCheck_2323_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_name_2305_);
lean_dec(v_linterOption_2295_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2323_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2309_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1);
lean_inc(v_name_2305_);
v___x_2310_ = l_Lean_MessageData_ofName(v_name_2305_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set_tag(v___x_2307_, 7);
lean_ctor_set(v___x_2307_, 1, v___x_2310_);
lean_ctor_set(v___x_2307_, 0, v___x_2309_);
v___x_2312_ = v___x_2307_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_disable_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2313_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v_disable_2315_ = l_Lean_MessageData_note(v___x_2314_);
v___x_2316_ = l_Lean_Linter_linterMessageTag;
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_msg_2297_);
lean_ctor_set(v___x_2317_, 1, v_disable_2315_);
v___x_2318_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_name_2305_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_inc(v_stx_2296_);
v___x_2320_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2320_, 0, v_stx_2296_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(v_stx_2296_, v___x_2320_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v_stx_2296_);
return v___x_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___boxed(lean_object* v_linterOption_2325_, lean_object* v_stx_2326_, lean_object* v_msg_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(v_linterOption_2325_, v_stx_2326_, v_msg_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(lean_object* v_linterOption_2336_, lean_object* v_stx_2337_, lean_object* v_msg_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2357_; 
v___x_2346_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2357_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2357_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
uint8_t v___x_2351_; 
v___x_2351_ = l_Lean_Linter_getLinterValue(v_linterOption_2336_, v_a_2347_);
lean_dec(v_a_2347_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec_ref(v_msg_2338_);
lean_dec(v_stx_2337_);
lean_dec_ref(v_linterOption_2336_);
v___x_2352_ = lean_box(0);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2352_);
v___x_2354_ = v___x_2349_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
else
{
lean_object* v___x_2356_; 
lean_del_object(v___x_2349_);
v___x_2356_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(v_linterOption_2336_, v_stx_2337_, v_msg_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___boxed(lean_object* v_linterOption_2358_, lean_object* v_stx_2359_, lean_object* v_msg_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v_linterOption_2358_, v_stx_2359_, v_msg_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2368_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(lean_object* v_head_2377_, lean_object* v___x_2378_, lean_object* v_unusedParams_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_ref_2387_; lean_object* v_name_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___y_2393_; lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v_ref_2387_ = lean_ctor_get(v___y_2384_, 2);
v_name_2388_ = lean_ctor_get(v_head_2377_, 0);
lean_inc(v_name_2388_);
lean_dec_ref(v_head_2377_);
lean_inc_ref(v_unusedParams_2379_);
v___x_2389_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(v_name_2388_, v_unusedParams_2379_);
v___x_2390_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2399_ = lean_array_get_size(v_unusedParams_2379_);
lean_dec_ref(v_unusedParams_2379_);
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_nat_dec_eq(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4));
v___y_2393_ = v___x_2402_;
goto v___jp_2392_;
}
else
{
lean_object* v___x_2403_; 
v___x_2403_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5));
v___y_2393_ = v___x_2403_;
goto v___jp_2392_;
}
v___jp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_inc_ref(v___y_2393_);
v___x_2394_ = l_Lean_stringToMessageData(v___y_2393_);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2391_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
lean_inc(v_ref_2387_);
v___x_2398_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_2378_, v_ref_2387_, v___x_2397_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2398_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed(lean_object* v_head_2404_, lean_object* v___x_2405_, lean_object* v_unusedParams_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(v_head_2404_, v___x_2405_, v_unusedParams_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(lean_object* v_as_x27_2415_, lean_object* v_b_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
if (lean_obj_tag(v_as_x27_2415_) == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v_b_2416_);
return v___x_2424_;
}
else
{
lean_object* v_head_2425_; lean_object* v_tail_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v_head_2425_ = lean_ctor_get(v_as_x27_2415_, 0);
v_tail_2426_ = lean_ctor_get(v_as_x27_2415_, 1);
v___x_2427_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
lean_inc_n(v_head_2425_, 2);
v___f_2428_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2428_, 0, v_head_2425_);
lean_closure_set(v___f_2428_, 1, v___x_2427_);
v___x_2429_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0));
v___x_2430_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_head_2425_, v___x_2429_, v___f_2428_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2431_; 
lean_dec_ref_known(v___x_2430_, 1);
v___x_2431_ = lean_box(0);
v_as_x27_2415_ = v_tail_2426_;
v_b_2416_ = v___x_2431_;
goto _start;
}
else
{
return v___x_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___boxed(lean_object* v_as_x27_2433_, lean_object* v_b_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_2433_, v_b_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v_as_x27_2433_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(lean_object* v___x_2443_, lean_object* v___x_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v___x_2443_, v___x_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v___x_2452_, 0);
lean_dec(v_unused_2460_);
v___x_2454_ = v___x_2452_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v___x_2452_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2444_);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2444_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
return v___x_2452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed(lean_object* v___x_2461_, lean_object* v___x_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(v___x_2461_, v___x_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___x_2461_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(lean_object* v___x_2471_, uint8_t v___x_2472_, lean_object* v_as_2473_, size_t v_sz_2474_, size_t v_i_2475_, lean_object* v_b_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
uint8_t v___x_2480_; 
v___x_2480_ = lean_usize_dec_lt(v_i_2475_, v_sz_2474_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
lean_dec_ref(v___x_2471_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_b_2476_);
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; lean_object* v_a_2484_; lean_object* v___x_2489_; lean_object* v_a_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
lean_dec_ref(v_b_2476_);
v___x_2482_ = lean_box(0);
v___x_2489_ = lean_box(0);
v_a_2490_ = lean_array_uget_borrowed(v_as_2473_, v_i_2475_);
lean_inc_ref(v___x_2471_);
lean_inc(v_a_2490_);
v___x_2491_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2490_, v___x_2471_);
v___x_2492_ = lean_box(0);
v___x_2493_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2472_, v___x_2491_, v___x_2492_);
v___x_2494_ = l_List_isEmpty___redArg(v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___f_2495_; lean_object* v___x_2496_; 
v___f_2495_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2495_, 0, v___x_2493_);
lean_closure_set(v___f_2495_, 1, v___x_2489_);
v___x_2496_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2495_, v___y_2477_, v___y_2478_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_dec_ref_known(v___x_2496_, 1);
v_a_2484_ = v___x_2489_;
goto v___jp_2483_;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec_ref(v___x_2471_);
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_dec(v___x_2493_);
v_a_2484_ = v___x_2489_;
goto v___jp_2483_;
}
v___jp_2483_:
{
lean_object* v___x_2485_; size_t v___x_2486_; size_t v___x_2487_; 
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2482_);
lean_ctor_set(v___x_2485_, 1, v_a_2484_);
v___x_2486_ = ((size_t)1ULL);
v___x_2487_ = lean_usize_add(v_i_2475_, v___x_2486_);
v_i_2475_ = v___x_2487_;
v_b_2476_ = v___x_2485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14___boxed(lean_object* v___x_2505_, lean_object* v___x_2506_, lean_object* v_as_2507_, lean_object* v_sz_2508_, lean_object* v_i_2509_, lean_object* v_b_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
uint8_t v___x_12193__boxed_2514_; size_t v_sz_boxed_2515_; size_t v_i_boxed_2516_; lean_object* v_res_2517_; 
v___x_12193__boxed_2514_ = lean_unbox(v___x_2506_);
v_sz_boxed_2515_ = lean_unbox_usize(v_sz_2508_);
lean_dec(v_sz_2508_);
v_i_boxed_2516_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_2505_, v___x_12193__boxed_2514_, v_as_2507_, v_sz_boxed_2515_, v_i_boxed_2516_, v_b_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v_as_2507_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(lean_object* v___x_2521_, uint8_t v___x_2522_, lean_object* v_as_2523_, size_t v_sz_2524_, size_t v_i_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_usize_dec_lt(v_i_2525_, v_sz_2524_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
lean_dec_ref(v___x_2521_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_b_2526_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
lean_dec_ref(v_b_2526_);
v___x_2532_ = lean_box(0);
v_a_2538_ = lean_array_uget_borrowed(v_as_2523_, v_i_2525_);
lean_inc_ref(v___x_2521_);
lean_inc(v_a_2538_);
v___x_2539_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2538_, v___x_2521_);
v___x_2540_ = lean_box(0);
v___x_2541_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2522_, v___x_2539_, v___x_2540_);
v___x_2542_ = l_List_isEmpty___redArg(v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___f_2543_; lean_object* v___x_2544_; 
v___f_2543_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2543_, 0, v___x_2541_);
lean_closure_set(v___f_2543_, 1, v___x_2532_);
v___x_2544_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2543_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_dec_ref_known(v___x_2544_, 1);
goto v___jp_2533_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v___x_2521_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
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
else
{
lean_dec(v___x_2541_);
goto v___jp_2533_;
}
v___jp_2533_:
{
lean_object* v___x_2534_; size_t v___x_2535_; size_t v___x_2536_; lean_object* v___x_2537_; 
v___x_2534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0));
v___x_2535_ = ((size_t)1ULL);
v___x_2536_ = lean_usize_add(v_i_2525_, v___x_2535_);
v___x_2537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_2521_, v___x_2522_, v_as_2523_, v_sz_2524_, v___x_2536_, v___x_2534_, v___y_2527_, v___y_2528_);
return v___x_2537_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___boxed(lean_object* v___x_2553_, lean_object* v___x_2554_, lean_object* v_as_2555_, lean_object* v_sz_2556_, lean_object* v_i_2557_, lean_object* v_b_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
uint8_t v___x_12263__boxed_2562_; size_t v_sz_boxed_2563_; size_t v_i_boxed_2564_; lean_object* v_res_2565_; 
v___x_12263__boxed_2562_ = lean_unbox(v___x_2554_);
v_sz_boxed_2563_ = lean_unbox_usize(v_sz_2556_);
lean_dec(v_sz_2556_);
v_i_boxed_2564_ = lean_unbox_usize(v_i_2557_);
lean_dec(v_i_2557_);
v_res_2565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_2553_, v___x_12263__boxed_2562_, v_as_2555_, v_sz_boxed_2563_, v_i_boxed_2564_, v_b_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec_ref(v_as_2555_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(lean_object* v_init_2566_, lean_object* v___x_2567_, uint8_t v___x_2568_, lean_object* v_n_2569_, lean_object* v_b_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
if (lean_obj_tag(v_n_2569_) == 0)
{
lean_object* v_cs_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; size_t v_sz_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v_cs_2574_ = lean_ctor_get(v_n_2569_, 0);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set(v___x_2576_, 1, v_b_2570_);
v_sz_2577_ = lean_array_size(v_cs_2574_);
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_2566_, v___x_2567_, v___x_2568_, v_cs_2574_, v_sz_2577_, v___x_2578_, v___x_2576_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2594_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2594_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2594_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v_fst_2584_; 
v_fst_2584_ = lean_ctor_get(v_a_2580_, 0);
if (lean_obj_tag(v_fst_2584_) == 0)
{
lean_object* v_snd_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
v_snd_2585_ = lean_ctor_get(v_a_2580_, 1);
lean_inc(v_snd_2585_);
lean_dec(v_a_2580_);
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_snd_2585_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2586_);
v___x_2588_ = v___x_2582_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
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
lean_object* v_val_2590_; lean_object* v___x_2592_; 
lean_inc_ref(v_fst_2584_);
lean_dec(v_a_2580_);
v_val_2590_ = lean_ctor_get(v_fst_2584_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v_fst_2584_, 1);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v_val_2590_);
v___x_2592_ = v___x_2582_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_val_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
v_a_2595_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2579_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2579_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
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
lean_object* v_vs_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; size_t v_sz_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v_vs_2603_ = lean_ctor_get(v_n_2569_, 0);
v___x_2604_ = lean_box(0);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
lean_ctor_set(v___x_2605_, 1, v_b_2570_);
v_sz_2606_ = lean_array_size(v_vs_2603_);
v___x_2607_ = ((size_t)0ULL);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_2567_, v___x_2568_, v_vs_2603_, v_sz_2606_, v___x_2607_, v___x_2605_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2623_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2623_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2623_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v_fst_2613_; 
v_fst_2613_ = lean_ctor_get(v_a_2609_, 0);
if (lean_obj_tag(v_fst_2613_) == 0)
{
lean_object* v_snd_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
v_snd_2614_ = lean_ctor_get(v_a_2609_, 1);
lean_inc(v_snd_2614_);
lean_dec(v_a_2609_);
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_snd_2614_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2615_);
v___x_2617_ = v___x_2611_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
else
{
lean_object* v_val_2619_; lean_object* v___x_2621_; 
lean_inc_ref(v_fst_2613_);
lean_dec(v_a_2609_);
v_val_2619_ = lean_ctor_get(v_fst_2613_, 0);
lean_inc(v_val_2619_);
lean_dec_ref_known(v_fst_2613_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_val_2619_);
v___x_2621_ = v___x_2611_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_val_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
v_a_2624_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2608_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2608_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(lean_object* v_init_2632_, lean_object* v___x_2633_, uint8_t v___x_2634_, lean_object* v_as_2635_, size_t v_sz_2636_, size_t v_i_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_usize_dec_lt(v_i_2637_, v_sz_2636_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
lean_dec_ref(v___x_2633_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_b_2638_);
return v___x_2643_;
}
else
{
lean_object* v_snd_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2678_; 
v_snd_2644_ = lean_ctor_get(v_b_2638_, 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_b_2638_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v_b_2638_, 0);
lean_dec(v_unused_2679_);
v___x_2646_ = v_b_2638_;
v_isShared_2647_ = v_isSharedCheck_2678_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_snd_2644_);
lean_dec(v_b_2638_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2678_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_a_2648_; lean_object* v___x_2649_; 
v_a_2648_ = lean_array_uget_borrowed(v_as_2635_, v_i_2637_);
lean_inc(v_snd_2644_);
lean_inc_ref(v___x_2633_);
v___x_2649_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2632_, v___x_2633_, v___x_2634_, v_a_2648_, v_snd_2644_, v___y_2639_, v___y_2640_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2669_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2669_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2669_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
if (lean_obj_tag(v_a_2650_) == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_dec_ref(v___x_2633_);
v___x_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_a_2650_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2654_);
v___x_2656_ = v___x_2646_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_snd_2644_);
v___x_2656_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2658_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2656_);
v___x_2658_ = v___x_2652_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
lean_del_object(v___x_2652_);
lean_dec(v_snd_2644_);
v_a_2661_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v_a_2650_, 1);
v___x_2662_ = lean_box(0);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v_a_2661_);
lean_ctor_set(v___x_2646_, 0, v___x_2662_);
v___x_2664_ = v___x_2646_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_a_2661_);
v___x_2664_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
size_t v___x_2665_; size_t v___x_2666_; 
v___x_2665_ = ((size_t)1ULL);
v___x_2666_ = lean_usize_add(v_i_2637_, v___x_2665_);
v_i_2637_ = v___x_2666_;
v_b_2638_ = v___x_2664_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_del_object(v___x_2646_);
lean_dec(v_snd_2644_);
lean_dec_ref(v___x_2633_);
v_a_2670_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2649_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2649_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11___boxed(lean_object* v_init_2680_, lean_object* v___x_2681_, lean_object* v___x_2682_, lean_object* v_as_2683_, lean_object* v_sz_2684_, lean_object* v_i_2685_, lean_object* v_b_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
uint8_t v___x_12326__boxed_2690_; size_t v_sz_boxed_2691_; size_t v_i_boxed_2692_; lean_object* v_res_2693_; 
v___x_12326__boxed_2690_ = lean_unbox(v___x_2682_);
v_sz_boxed_2691_ = lean_unbox_usize(v_sz_2684_);
lean_dec(v_sz_2684_);
v_i_boxed_2692_ = lean_unbox_usize(v_i_2685_);
lean_dec(v_i_2685_);
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_2680_, v___x_2681_, v___x_12326__boxed_2690_, v_as_2683_, v_sz_boxed_2691_, v_i_boxed_2692_, v_b_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v_as_2683_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8___boxed(lean_object* v_init_2694_, lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v_n_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
uint8_t v___x_12347__boxed_2702_; lean_object* v_res_2703_; 
v___x_12347__boxed_2702_ = lean_unbox(v___x_2696_);
v_res_2703_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2694_, v___x_2695_, v___x_12347__boxed_2702_, v_n_2697_, v_b_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec_ref(v_n_2697_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(lean_object* v___x_2704_, uint8_t v___x_2705_, lean_object* v_as_2706_, size_t v_sz_2707_, size_t v_i_2708_, lean_object* v_b_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_usize_dec_lt(v_i_2708_, v_sz_2707_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
lean_dec_ref(v___x_2704_);
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v_b_2709_);
return v___x_2714_;
}
else
{
lean_object* v___x_2715_; lean_object* v_a_2717_; lean_object* v___x_2722_; lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
lean_dec_ref(v_b_2709_);
v___x_2715_ = lean_box(0);
v___x_2722_ = lean_box(0);
v_a_2723_ = lean_array_uget_borrowed(v_as_2706_, v_i_2708_);
lean_inc_ref(v___x_2704_);
lean_inc(v_a_2723_);
v___x_2724_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2723_, v___x_2704_);
v___x_2725_ = lean_box(0);
v___x_2726_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2705_, v___x_2724_, v___x_2725_);
v___x_2727_ = l_List_isEmpty___redArg(v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___f_2728_; lean_object* v___x_2729_; 
v___f_2728_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2728_, 0, v___x_2726_);
lean_closure_set(v___f_2728_, 1, v___x_2722_);
v___x_2729_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2728_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_dec_ref_known(v___x_2729_, 1);
v_a_2717_ = v___x_2722_;
goto v___jp_2716_;
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v___x_2704_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_dec(v___x_2726_);
v_a_2717_ = v___x_2722_;
goto v___jp_2716_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; size_t v___x_2719_; size_t v___x_2720_; 
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2715_);
lean_ctor_set(v___x_2718_, 1, v_a_2717_);
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2708_, v___x_2719_);
v_i_2708_ = v___x_2720_;
v_b_2709_ = v___x_2718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14___boxed(lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v_as_2740_, lean_object* v_sz_2741_, lean_object* v_i_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
uint8_t v___x_12533__boxed_2747_; size_t v_sz_boxed_2748_; size_t v_i_boxed_2749_; lean_object* v_res_2750_; 
v___x_12533__boxed_2747_ = lean_unbox(v___x_2739_);
v_sz_boxed_2748_ = lean_unbox_usize(v_sz_2741_);
lean_dec(v_sz_2741_);
v_i_boxed_2749_ = lean_unbox_usize(v_i_2742_);
lean_dec(v_i_2742_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_2738_, v___x_12533__boxed_2747_, v_as_2740_, v_sz_boxed_2748_, v_i_boxed_2749_, v_b_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v_as_2740_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(lean_object* v___x_2754_, uint8_t v___x_2755_, lean_object* v_as_2756_, size_t v_sz_2757_, size_t v_i_2758_, lean_object* v_b_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_lt(v_i_2758_, v_sz_2757_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
lean_dec_ref(v___x_2754_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_b_2759_);
return v___x_2764_;
}
else
{
lean_object* v___x_2765_; lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
lean_dec_ref(v_b_2759_);
v___x_2765_ = lean_box(0);
v_a_2771_ = lean_array_uget_borrowed(v_as_2756_, v_i_2758_);
lean_inc_ref(v___x_2754_);
lean_inc(v_a_2771_);
v___x_2772_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2771_, v___x_2754_);
v___x_2773_ = lean_box(0);
v___x_2774_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2755_, v___x_2772_, v___x_2773_);
v___x_2775_ = l_List_isEmpty___redArg(v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___f_2776_; lean_object* v___x_2777_; 
v___f_2776_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2776_, 0, v___x_2774_);
lean_closure_set(v___f_2776_, 1, v___x_2765_);
v___x_2777_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2776_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_dec_ref_known(v___x_2777_, 1);
goto v___jp_2766_;
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v___x_2754_);
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_dec(v___x_2774_);
goto v___jp_2766_;
}
v___jp_2766_:
{
lean_object* v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; lean_object* v___x_2770_; 
v___x_2767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0));
v___x_2768_ = ((size_t)1ULL);
v___x_2769_ = lean_usize_add(v_i_2758_, v___x_2768_);
v___x_2770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_2754_, v___x_2755_, v_as_2756_, v_sz_2757_, v___x_2769_, v___x_2767_, v___y_2760_, v___y_2761_);
return v___x_2770_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___boxed(lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v_as_2788_, lean_object* v_sz_2789_, lean_object* v_i_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v___x_12603__boxed_2795_; size_t v_sz_boxed_2796_; size_t v_i_boxed_2797_; lean_object* v_res_2798_; 
v___x_12603__boxed_2795_ = lean_unbox(v___x_2787_);
v_sz_boxed_2796_ = lean_unbox_usize(v_sz_2789_);
lean_dec(v_sz_2789_);
v_i_boxed_2797_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_res_2798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_2786_, v___x_12603__boxed_2795_, v_as_2788_, v_sz_boxed_2796_, v_i_boxed_2797_, v_b_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_as_2788_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(lean_object* v___x_2799_, uint8_t v___x_2800_, lean_object* v_t_2801_, lean_object* v_init_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_root_2806_; lean_object* v_tail_2807_; lean_object* v___x_2808_; 
v_root_2806_ = lean_ctor_get(v_t_2801_, 0);
v_tail_2807_ = lean_ctor_get(v_t_2801_, 1);
lean_inc_ref(v___x_2799_);
v___x_2808_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2802_, v___x_2799_, v___x_2800_, v_root_2806_, v_init_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2845_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2845_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2845_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; 
lean_dec_ref(v___x_2799_);
v_a_2813_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v_a_2809_, 1);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v_a_2813_);
v___x_2815_ = v___x_2811_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; size_t v_sz_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
lean_del_object(v___x_2811_);
v_a_2817_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v_a_2809_, 1);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v_a_2817_);
v_sz_2820_ = lean_array_size(v_tail_2807_);
v___x_2821_ = ((size_t)0ULL);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_2799_, v___x_2800_, v_tail_2807_, v_sz_2820_, v___x_2821_, v___x_2819_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2836_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2836_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2836_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v_fst_2827_; 
v_fst_2827_ = lean_ctor_get(v_a_2823_, 0);
if (lean_obj_tag(v_fst_2827_) == 0)
{
lean_object* v_snd_2828_; lean_object* v___x_2830_; 
v_snd_2828_ = lean_ctor_get(v_a_2823_, 1);
lean_inc(v_snd_2828_);
lean_dec(v_a_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_snd_2828_);
v___x_2830_ = v___x_2825_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_snd_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
else
{
lean_object* v_val_2832_; lean_object* v___x_2834_; 
lean_inc_ref(v_fst_2827_);
lean_dec(v_a_2823_);
v_val_2832_ = lean_ctor_get(v_fst_2827_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_fst_2827_, 1);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_val_2832_);
v___x_2834_ = v___x_2825_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_val_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
v_a_2837_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2822_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2822_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v___x_2799_);
v_a_2846_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2808_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2808_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5___boxed(lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v_t_2856_, lean_object* v_init_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v___x_12666__boxed_2861_; lean_object* v_res_2862_; 
v___x_12666__boxed_2861_ = lean_unbox(v___x_2855_);
v_res_2862_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v___x_2854_, v___x_12666__boxed_2861_, v_t_2856_, v_init_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec_ref(v_t_2856_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(lean_object* v_o_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; lean_object* v_env_2867_; lean_object* v___x_2868_; lean_object* v_toEnvExtension_2869_; lean_object* v_asyncMode_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v_merged_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2882_; 
v___x_2866_ = lean_st_ref_get(v___y_2864_);
v_env_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc_ref(v_env_2867_);
lean_dec(v___x_2866_);
v___x_2868_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2869_ = lean_ctor_get(v___x_2868_, 0);
v_asyncMode_2870_ = lean_ctor_get(v_toEnvExtension_2869_, 2);
v___x_2871_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2872_ = lean_box(0);
v___x_2873_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2871_, v___x_2868_, v_env_2867_, v_asyncMode_2870_, v___x_2872_);
v_merged_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; 
v_unused_2883_ = lean_ctor_get(v___x_2873_, 1);
lean_dec(v_unused_2883_);
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2882_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_merged_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2882_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v_merged_2874_);
lean_ctor_set(v___x_2876_, 0, v_o_2863_);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_o_2863_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_merged_2874_);
v___x_2879_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_2884_, v___y_2885_);
lean_dec(v___y_2885_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___x_2891_; lean_object* v_scopes_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v_opts_2895_; lean_object* v___x_2896_; 
v___x_2891_ = lean_st_ref_get(v___y_2889_);
v_scopes_2892_ = lean_ctor_get(v___x_2891_, 2);
lean_inc(v_scopes_2892_);
lean_dec(v___x_2891_);
v___x_2893_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2894_ = l_List_head_x21___redArg(v___x_2893_, v_scopes_2892_);
lean_dec(v_scopes_2892_);
v_opts_2895_ = lean_ctor_get(v___x_2894_, 1);
lean_inc_ref(v_opts_2895_);
lean_dec(v___x_2894_);
v___x_2896_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_opts_2895_, v___y_2889_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0___boxed(lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(lean_object* v_x_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2942_; 
v___x_2905_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_2902_, v___y_2903_);
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2942_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2942_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; uint8_t v___y_2912_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2910_ = lean_st_ref_get(v___y_2903_);
v___x_2938_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
v___x_2939_ = l_Lean_Linter_getLinterValue(v___x_2938_, v_a_2906_);
lean_dec(v_a_2906_);
if (v___x_2939_ == 0)
{
lean_dec(v___x_2910_);
v___y_2912_ = v___x_2939_;
goto v___jp_2911_;
}
else
{
lean_object* v_infoState_2940_; uint8_t v_enabled_2941_; 
v_infoState_2940_ = lean_ctor_get(v___x_2910_, 8);
lean_inc_ref(v_infoState_2940_);
lean_dec(v___x_2910_);
v_enabled_2941_ = lean_ctor_get_uint8(v_infoState_2940_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2940_);
v___y_2912_ = v_enabled_2941_;
goto v___jp_2911_;
}
v___jp_2911_:
{
if (v___y_2912_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2913_ = lean_box(0);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2913_);
v___x_2915_ = v___x_2908_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
else
{
lean_object* v___x_2917_; lean_object* v_messages_2918_; uint8_t v___x_2919_; 
v___x_2917_ = lean_st_ref_get(v___y_2903_);
v_messages_2918_ = lean_ctor_get(v___x_2917_, 1);
lean_inc_ref(v_messages_2918_);
lean_dec(v___x_2917_);
v___x_2919_ = l_Lean_MessageLog_hasErrors(v_messages_2918_);
lean_dec_ref(v_messages_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v_a_2922_; lean_object* v_env_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_del_object(v___x_2908_);
v___x_2920_ = lean_st_ref_get(v___y_2903_);
v___x_2921_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_2903_);
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref(v___x_2921_);
v_env_2923_ = lean_ctor_get(v___x_2920_, 0);
lean_inc_ref(v_env_2923_);
lean_dec(v___x_2920_);
v___x_2924_ = lean_box(0);
v___x_2925_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v_env_2923_, v___x_2919_, v_a_2922_, v___x_2924_, v___y_2902_, v___y_2903_);
lean_dec(v_a_2922_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2925_, 0);
lean_dec(v_unused_2933_);
v___x_2927_ = v___x_2925_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_dec(v___x_2925_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2924_);
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2924_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
else
{
return v___x_2925_;
}
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2936_; 
v___x_2934_ = lean_box(0);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2934_);
v___x_2936_ = v___x_2908_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0___boxed(lean_object* v_x_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(v_x_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v_x_2943_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(lean_object* v_o_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_2963_, v___y_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___boxed(lean_object* v_o_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(v_o_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(lean_object* v_as_2973_, lean_object* v_as_x27_2974_, lean_object* v_b_2975_, lean_object* v_a_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_2974_, v_b_2975_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___boxed(lean_object* v_as_2985_, lean_object* v_as_x27_2986_, lean_object* v_b_2987_, lean_object* v_a_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(v_as_2985_, v_as_x27_2986_, v_b_2987_, v_a_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v_as_x27_2986_);
lean_dec(v_as_2985_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(lean_object* v_o_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_o_2997_, v___y_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_o_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(v_o_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(lean_object* v_ref_3015_, lean_object* v_msgData_3016_, uint8_t v_severity_3017_, uint8_t v_isSilent_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_3015_, v_msgData_3016_, v_severity_3017_, v_isSilent_3018_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_ref_3027_, lean_object* v_msgData_3028_, lean_object* v_severity_3029_, lean_object* v_isSilent_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
uint8_t v_severity_boxed_3038_; uint8_t v_isSilent_boxed_3039_; lean_object* v_res_3040_; 
v_severity_boxed_3038_ = lean_unbox(v_severity_3029_);
v_isSilent_boxed_3039_ = lean_unbox(v_isSilent_3030_);
v_res_3040_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(v_ref_3027_, v_msgData_3028_, v_severity_boxed_3038_, v_isSilent_boxed_3039_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v_ref_3027_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = ((lean_object*)(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter));
v___x_3043_ = l_Lean_Elab_Command_addLinter(v___x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2____boxed(lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
return v_res_3045_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrivateName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrivateName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_Extra_linter_extra_unusedDecidableInType = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_unusedDecidableInType);
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Extra_UnusedDecidableInType(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* initialize_Lean_PrivateName(uint8_t builtin);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Extra_UnusedDecidableInType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
}
#ifdef __cplusplus
}
#endif
