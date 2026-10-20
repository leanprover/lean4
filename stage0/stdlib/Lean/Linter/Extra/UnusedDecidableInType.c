// Lean compiler output
// Module: Lean.Linter.Extra.UnusedDecidableInType
// Imports: public import Lean.Linter.Basic public import Lean.Meta.ForEachExpr public import Lean.Meta.Sorry public import Lean.PrivateName public import Lean.Elab.InfoTree.Util public import Lean.Linter.Util
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
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
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DecidablePred"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 236, 239, 206, 255, 167, 201, 157)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "DecidableRel"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(127, 165, 128, 103, 195, 117, 187, 51)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "DecidableEq"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 163, 7, 138, 119, 67, 2, 253)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "DecidableLE"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(33, 198, 120, 234, 95, 60, 229, 135)}};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "DecidableLT"};
static const lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(113, 2, 59, 91, 108, 226, 67, 238)}};
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v_binderType_18_; lean_object* v_body_19_; uint8_t v_binderInfo_20_; uint8_t v___x_21_; 
v_binderType_18_ = lean_ctor_get(v___x_17_, 1);
lean_inc_ref(v_binderType_18_);
v_body_19_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_body_19_);
v_binderInfo_20_ = lean_ctor_get_uint8(v___x_17_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_17_, 3);
v___x_21_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_20_);
if (v___x_21_ == 0)
{
lean_dec_ref(v_binderType_18_);
v_e_16_ = v_body_19_;
goto _start;
}
else
{
lean_object* v___x_23_; uint8_t v___x_24_; 
lean_inc_ref(v_p_15_);
v___x_23_ = lean_apply_1(v_p_15_, v_binderType_18_);
v___x_24_ = lean_unbox(v___x_23_);
if (v___x_24_ == 0)
{
v_e_16_ = v_body_19_;
goto _start;
}
else
{
uint8_t v___x_26_; 
lean_dec_ref(v_body_19_);
lean_dec_ref(v_p_15_);
v___x_26_ = lean_unbox(v___x_23_);
return v___x_26_;
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
lean_object* v_binderType_39_; lean_object* v_body_40_; uint8_t v_binderInfo_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v_binderType_39_ = lean_ctor_get(v___x_38_, 1);
lean_inc_ref(v_binderType_39_);
v_body_40_ = lean_ctor_get(v___x_38_, 2);
lean_inc_ref(v_body_40_);
v_binderInfo_41_ = lean_ctor_get_uint8(v___x_38_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_38_, 3);
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_current_36_, v___x_42_);
v___x_44_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_41_);
if (v___x_44_ == 0)
{
lean_dec_ref(v_binderType_39_);
lean_dec(v_current_36_);
v_body_35_ = v_body_40_;
v_current_36_ = v___x_43_;
goto _start;
}
else
{
lean_object* v___x_46_; uint8_t v___x_47_; 
lean_inc_ref(v_p_34_);
v___x_46_ = lean_apply_1(v_p_34_, v_binderType_39_);
v___x_47_ = lean_unbox(v___x_46_);
if (v___x_47_ == 0)
{
lean_dec(v_current_36_);
v_body_35_ = v_body_40_;
v_current_36_ = v___x_43_;
goto _start;
}
else
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_expr_has_loose_bvar(v_body_40_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
v___x_51_ = lean_array_push(v_acc_37_, v_current_36_);
v_body_35_ = v_body_40_;
v_current_36_ = v___x_43_;
v_acc_37_ = v___x_51_;
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
lean_object* v_body_54_; 
v_body_54_ = lean_ctor_get(v___x_38_, 3);
lean_inc_ref(v_body_54_);
lean_dec_ref_known(v___x_38_, 4);
v_body_35_ = v_body_54_;
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(lean_object* v_p_58_, lean_object* v_e_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0));
v___x_62_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(v_p_58_, v_e_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(lean_object* v_env_63_, lean_object* v_p_64_, lean_object* v_decl_65_, uint8_t v_skipRealize_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Environment_findAsync_x3f(v_env_63_, v_decl_65_, v_skipRealize_66_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v_p_64_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_82_; 
v_val_69_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_82_ == 0)
{
v___x_71_ = v___x_67_;
v_isShared_72_ = v_isSharedCheck_82_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v___x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_82_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint8_t v_kind_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_kind_73_ = lean_ctor_get_uint8(v_val_69_, sizeof(void*)*3);
v___x_74_ = lean_box(v_kind_73_);
v___x_75_ = lean_apply_1(v_p_64_, v___x_74_);
v___x_76_ = lean_unbox(v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
lean_del_object(v___x_71_);
lean_dec(v_val_69_);
v___x_77_ = lean_box(0);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = l_Lean_AsyncConstantInfo_toConstantVal(v_val_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_78_);
v___x_80_ = v___x_71_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f___boxed(lean_object* v_env_83_, lean_object* v_p_84_, lean_object* v_decl_85_, lean_object* v_skipRealize_86_){
_start:
{
uint8_t v_skipRealize_boxed_87_; lean_object* v_res_88_; 
v_skipRealize_boxed_87_ = lean_unbox(v_skipRealize_86_);
v_res_88_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_83_, v_p_84_, v_decl_85_, v_skipRealize_boxed_87_);
return v_res_88_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(uint8_t v_x_89_){
_start:
{
if (v_x_89_ == 1)
{
uint8_t v___x_90_; 
v___x_90_ = 1;
return v___x_90_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0___boxed(lean_object* v_x_92_){
_start:
{
uint8_t v_x_22__boxed_93_; uint8_t v_res_94_; lean_object* v_r_95_; 
v_x_22__boxed_93_ = lean_unbox(v_x_92_);
v_res_94_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(v_x_22__boxed_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(lean_object* v_env_97_, lean_object* v_decl_98_, uint8_t v_skipRealize_99_){
_start:
{
lean_object* v___f_100_; lean_object* v___x_101_; 
v___f_100_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0));
v___x_101_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_97_, v___f_100_, v_decl_98_, v_skipRealize_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___boxed(lean_object* v_env_102_, lean_object* v_decl_103_, lean_object* v_skipRealize_104_){
_start:
{
uint8_t v_skipRealize_boxed_105_; lean_object* v_res_106_; 
v_skipRealize_boxed_105_ = lean_unbox(v_skipRealize_104_);
v_res_106_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_102_, v_decl_103_, v_skipRealize_boxed_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(lean_object* v_name_107_, lean_object* v_decl_108_, lean_object* v_ref_109_){
_start:
{
lean_object* v_defValue_111_; lean_object* v_descr_112_; lean_object* v_deprecation_x3f_113_; lean_object* v___x_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_defValue_111_ = lean_ctor_get(v_decl_108_, 0);
v_descr_112_ = lean_ctor_get(v_decl_108_, 1);
v_deprecation_x3f_113_ = lean_ctor_get(v_decl_108_, 2);
v___x_114_ = lean_alloc_ctor(1, 0, 1);
v___x_115_ = lean_unbox(v_defValue_111_);
lean_ctor_set_uint8(v___x_114_, 0, v___x_115_);
lean_inc(v_deprecation_x3f_113_);
lean_inc_ref(v_descr_112_);
lean_inc_n(v_name_107_, 2);
v___x_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_116_, 0, v_name_107_);
lean_ctor_set(v___x_116_, 1, v_ref_109_);
lean_ctor_set(v___x_116_, 2, v___x_114_);
lean_ctor_set(v___x_116_, 3, v_descr_112_);
lean_ctor_set(v___x_116_, 4, v_deprecation_x3f_113_);
v___x_117_ = lean_register_option(v_name_107_, v___x_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_125_ == 0)
{
lean_object* v_unused_126_; 
v_unused_126_ = lean_ctor_get(v___x_117_, 0);
lean_dec(v_unused_126_);
v___x_119_ = v___x_117_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_dec(v___x_117_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
lean_inc(v_defValue_111_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_name_107_);
lean_ctor_set(v___x_121_, 1, v_defValue_111_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_name_107_);
v_a_127_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_117_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_117_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_135_, lean_object* v_decl_136_, lean_object* v_ref_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v_name_135_, v_decl_136_, v_ref_137_);
lean_dec_ref(v_decl_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_165_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_166_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_167_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v___x_164_, v___x_165_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4____boxed(lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
return v_res_169_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2));
v___x_175_ = l_Lean_stringToMessageData(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4));
v___x_178_ = l_Lean_stringToMessageData(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6));
v___x_181_ = l_Lean_stringToMessageData(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8));
v___x_184_ = l_Lean_stringToMessageData(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0(lean_object* v_param_185_){
_start:
{
lean_object* v_type_x3f_186_; lean_object* v_idx_187_; uint8_t v_appearsInTypeProof_188_; lean_object* v___y_190_; 
v_type_x3f_186_ = lean_ctor_get(v_param_185_, 1);
lean_inc(v_type_x3f_186_);
v_idx_187_ = lean_ctor_get(v_param_185_, 2);
lean_inc(v_idx_187_);
v_appearsInTypeProof_188_ = lean_ctor_get_uint8(v_param_185_, sizeof(void*)*3);
lean_dec_ref(v_param_185_);
if (lean_obj_tag(v_type_x3f_186_) == 1)
{
lean_object* v_val_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_212_; 
v_val_193_ = lean_ctor_get(v_type_x3f_186_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_type_x3f_186_);
if (v_isSharedCheck_212_ == 0)
{
v___x_195_ = v_type_x3f_186_;
v_isShared_196_ = v_isSharedCheck_212_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_val_193_);
lean_dec(v_type_x3f_186_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_212_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_197_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
v___x_198_ = l_Lean_MessageData_ofExpr(v_val_193_);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
v___x_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_idx_187_, v___x_202_);
lean_dec(v_idx_187_);
v___x_204_ = l_Nat_reprFast(v___x_203_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 3);
lean_ctor_set(v___x_195_, 0, v___x_204_);
v___x_206_ = v___x_195_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_211_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = l_Lean_MessageData_ofFormat(v___x_206_);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_201_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___y_190_ = v___x_210_;
goto v___jp_189_;
}
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_type_x3f_186_);
v___x_213_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_add(v_idx_187_, v___x_214_);
lean_dec(v_idx_187_);
v___x_216_ = l_Nat_reprFast(v___x_215_);
v___x_217_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
v___x_218_ = l_Lean_MessageData_ofFormat(v___x_217_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_213_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___y_190_ = v___x_219_;
goto v___jp_189_;
}
v___jp_189_:
{
if (v_appearsInTypeProof_188_ == 0)
{
return v___y_190_;
}
else
{
lean_object* v___x_191_; lean_object* v_msg_192_; 
v___x_191_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
v_msg_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_192_, 0, v___y_190_);
lean_ctor_set(v_msg_192_, 1, v___x_191_);
return v_msg_192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(lean_object* v_as_222_, size_t v_i_223_, size_t v_stop_224_, lean_object* v_b_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_usize_dec_eq(v_i_223_, v_stop_224_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; 
v___x_227_ = lean_array_uget_borrowed(v_as_222_, v_i_223_);
lean_inc(v___x_227_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v_b_225_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_223_, v___x_229_);
v_i_223_ = v___x_230_;
v_b_225_ = v___x_228_;
goto _start;
}
else
{
return v_b_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2___boxed(lean_object* v_as_232_, lean_object* v_i_233_, lean_object* v_stop_234_, lean_object* v_b_235_){
_start:
{
size_t v_i_boxed_236_; size_t v_stop_boxed_237_; lean_object* v_res_238_; 
v_i_boxed_236_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_stop_boxed_237_ = lean_unbox_usize(v_stop_234_);
lean_dec(v_stop_234_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v_as_232_, v_i_boxed_236_, v_stop_boxed_237_, v_b_235_);
lean_dec_ref(v_as_232_);
return v_res_238_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(lean_object* v_as_239_, size_t v_i_240_, size_t v_stop_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = lean_usize_dec_eq(v_i_240_, v_stop_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; uint8_t v_appearsInTypeProof_244_; 
v___x_243_ = lean_array_uget_borrowed(v_as_239_, v_i_240_);
v_appearsInTypeProof_244_ = lean_ctor_get_uint8(v___x_243_, sizeof(void*)*3);
if (v_appearsInTypeProof_244_ == 0)
{
size_t v___x_245_; size_t v___x_246_; 
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_add(v_i_240_, v___x_245_);
v_i_240_ = v___x_246_;
goto _start;
}
else
{
return v_appearsInTypeProof_244_;
}
}
else
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3___boxed(lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_stop_251_){
_start:
{
size_t v_i_boxed_252_; size_t v_stop_boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_i_boxed_252_ = lean_unbox_usize(v_i_250_);
lean_dec(v_i_250_);
v_stop_boxed_253_ = lean_unbox_usize(v_stop_251_);
lean_dec(v_stop_251_);
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_as_249_, v_i_boxed_252_, v_stop_boxed_253_);
lean_dec_ref(v_as_249_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(size_t v_sz_256_, size_t v_i_257_, lean_object* v_bs_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = lean_usize_dec_lt(v_i_257_, v_sz_256_);
if (v___x_259_ == 0)
{
return v_bs_258_;
}
else
{
lean_object* v_v_260_; lean_object* v_type_x3f_261_; lean_object* v_idx_262_; uint8_t v_appearsInTypeProof_263_; lean_object* v___x_264_; lean_object* v_bs_x27_265_; lean_object* v___y_267_; lean_object* v___y_273_; 
v_v_260_ = lean_array_uget_borrowed(v_bs_258_, v_i_257_);
v_type_x3f_261_ = lean_ctor_get(v_v_260_, 1);
lean_inc(v_type_x3f_261_);
v_idx_262_ = lean_ctor_get(v_v_260_, 2);
lean_inc(v_idx_262_);
v_appearsInTypeProof_263_ = lean_ctor_get_uint8(v_v_260_, sizeof(void*)*3);
v___x_264_ = lean_unsigned_to_nat(0u);
v_bs_x27_265_ = lean_array_uset(v_bs_258_, v_i_257_, v___x_264_);
if (lean_obj_tag(v_type_x3f_261_) == 1)
{
lean_object* v_val_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_295_; 
v_val_276_ = lean_ctor_get(v_type_x3f_261_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_type_x3f_261_);
if (v_isSharedCheck_295_ == 0)
{
v___x_278_ = v_type_x3f_261_;
v_isShared_279_ = v_isSharedCheck_295_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_val_276_);
lean_dec(v_type_x3f_261_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_295_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_280_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
v___x_281_ = l_Lean_MessageData_ofExpr(v_val_276_);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_idx_262_, v___x_285_);
lean_dec(v_idx_262_);
v___x_287_ = l_Nat_reprFast(v___x_286_);
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 3);
lean_ctor_set(v___x_278_, 0, v___x_287_);
v___x_289_ = v___x_278_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_294_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = l_Lean_MessageData_ofFormat(v___x_289_);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_284_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___y_273_ = v___x_293_;
goto v___jp_272_;
}
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_type_x3f_261_);
v___x_296_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_idx_262_, v___x_297_);
lean_dec(v_idx_262_);
v___x_299_ = l_Nat_reprFast(v___x_298_);
v___x_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___x_301_ = l_Lean_MessageData_ofFormat(v___x_300_);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_296_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___y_273_ = v___x_302_;
goto v___jp_272_;
}
v___jp_266_:
{
size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_add(v_i_257_, v___x_268_);
v___x_270_ = lean_array_uset(v_bs_x27_265_, v_i_257_, v___y_267_);
v_i_257_ = v___x_269_;
v_bs_258_ = v___x_270_;
goto _start;
}
v___jp_272_:
{
if (v_appearsInTypeProof_263_ == 0)
{
v___y_267_ = v___y_273_;
goto v___jp_266_;
}
else
{
lean_object* v___x_274_; lean_object* v_msg_275_; 
v___x_274_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
v_msg_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_275_, 0, v___y_273_);
lean_ctor_set(v_msg_275_, 1, v___x_274_);
v___y_267_ = v_msg_275_;
goto v___jp_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0___boxed(lean_object* v_sz_303_, lean_object* v_i_304_, lean_object* v_bs_305_){
_start:
{
size_t v_sz_boxed_306_; size_t v_i_boxed_307_; lean_object* v_res_308_; 
v_sz_boxed_306_ = lean_unbox_usize(v_sz_303_);
lean_dec(v_sz_303_);
v_i_boxed_307_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_res_308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_boxed_306_, v_i_boxed_307_, v_bs_305_);
return v_res_308_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(size_t v_sz_312_, size_t v_i_313_, lean_object* v_bs_314_){
_start:
{
uint8_t v___x_315_; 
v___x_315_ = lean_usize_dec_lt(v_i_313_, v_sz_312_);
if (v___x_315_ == 0)
{
return v_bs_314_;
}
else
{
lean_object* v_v_316_; lean_object* v___x_317_; lean_object* v_bs_x27_318_; lean_object* v___x_319_; lean_object* v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v_v_316_ = lean_array_uget(v_bs_314_, v_i_313_);
v___x_317_ = lean_unsigned_to_nat(0u);
v_bs_x27_318_ = lean_array_uset(v_bs_314_, v_i_313_, v___x_317_);
v___x_319_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_v_316_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_add(v_i_313_, v___x_321_);
v___x_323_ = lean_array_uset(v_bs_x27_318_, v_i_313_, v___x_320_);
v_i_313_ = v___x_322_;
v_bs_314_ = v___x_323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___boxed(lean_object* v_sz_325_, lean_object* v_i_326_, lean_object* v_bs_327_){
_start:
{
size_t v_sz_boxed_328_; size_t v_i_boxed_329_; lean_object* v_res_330_; 
v_sz_boxed_328_ = lean_unbox_usize(v_sz_325_);
lean_dec(v_sz_325_);
v_i_boxed_329_ = lean_unbox_usize(v_i_326_);
lean_dec(v_i_326_);
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_boxed_328_, v_i_boxed_329_, v_bs_327_);
return v_res_330_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(lean_object* v_declName_347_, lean_object* v_unusedInstanceBinders_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___y_351_; lean_object* v___y_352_; size_t v___y_353_; lean_object* v___y_354_; lean_object* v___y_369_; uint8_t v___y_370_; size_t v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; uint8_t v___y_381_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_array_get_size(v_unusedInstanceBinders_348_);
v___x_397_ = lean_nat_dec_lt(v___x_349_, v___x_396_);
if (v___x_397_ == 0)
{
v___y_381_ = v___x_397_;
goto v___jp_380_;
}
else
{
if (v___x_397_ == 0)
{
v___y_381_ = v___x_397_;
goto v___jp_380_;
}
else
{
size_t v___x_398_; size_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = ((size_t)0ULL);
v___x_399_ = lean_usize_of_nat(v___x_396_);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_unusedInstanceBinders_348_, v___x_398_, v___x_399_);
v___y_381_ = v___x_400_;
goto v___jp_380_;
}
}
v___jp_350_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; size_t v_sz_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
lean_inc_ref(v___y_354_);
v___x_355_ = l_Lean_stringToMessageData(v___y_354_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___y_352_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_MessageData_nil;
v_sz_360_ = lean_array_size(v___y_351_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_360_, v___y_353_, v___y_351_);
v___x_362_ = lean_array_get_size(v___x_361_);
v___x_363_ = lean_nat_dec_lt(v___x_349_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v___x_361_);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_358_);
lean_ctor_set(v___x_364_, 1, v___x_359_);
return v___x_364_;
}
else
{
size_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_usize_of_nat(v___x_362_);
v___x_366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v___x_361_, v___y_353_, v___x_365_, v___x_359_);
lean_dec_ref(v___x_361_);
v___x_367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_358_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
v___jp_368_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_inc_ref(v___y_373_);
v___x_374_ = l_Lean_stringToMessageData(v___y_373_);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___y_372_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
if (v___y_370_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4));
v___y_351_ = v___y_369_;
v___y_352_ = v___x_377_;
v___y_353_ = v___y_371_;
v___y_354_ = v___x_378_;
goto v___jp_350_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5));
v___y_351_ = v___y_369_;
v___y_352_ = v___x_377_;
v___y_353_ = v___y_371_;
v___y_354_ = v___x_379_;
goto v___jp_350_;
}
}
v___jp_380_:
{
size_t v_sz_382_; size_t v___x_383_; lean_object* v_unusedInstanceBinders_384_; lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_sz_382_ = lean_array_size(v_unusedInstanceBinders_348_);
v___x_383_ = ((size_t)0ULL);
v_unusedInstanceBinders_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_382_, v___x_383_, v_unusedInstanceBinders_348_);
v___x_385_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7);
v___x_386_ = 0;
v___x_387_ = l_Lean_MessageData_ofConstName(v_declName_347_, v___x_386_);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_385_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_array_get_size(v_unusedInstanceBinders_384_);
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_dec_eq(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10));
v___y_369_ = v_unusedInstanceBinders_384_;
v___y_370_ = v___y_381_;
v___y_371_ = v___x_383_;
v___y_372_ = v___x_390_;
v___y_373_ = v___x_394_;
goto v___jp_368_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11));
v___y_369_ = v_unusedInstanceBinders_384_;
v___y_370_ = v___y_381_;
v___y_371_ = v___x_383_;
v___y_372_ = v___x_390_;
v___y_373_ = v___x_395_;
goto v___jp_368_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(lean_object* v_subExpr_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_Expr_hasFVar(v_subExpr_401_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref(v_subExpr_401_);
v___x_409_ = lean_box(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
else
{
uint8_t v___x_411_; 
v___x_411_ = l_Lean_Expr_isSorry(v_subExpr_401_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_inc_ref(v_subExpr_401_);
v___x_412_ = l_Lean_Meta_isProof(v_subExpr_401_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_433_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_433_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_433_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_433_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
uint8_t v___x_417_; 
v___x_417_ = lean_unbox(v_a_413_);
if (v___x_417_ == 0)
{
if (lean_obj_tag(v_subExpr_401_) == 1)
{
lean_object* v_fvarId_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v_fvarId_418_ = lean_ctor_get(v_subExpr_401_, 0);
lean_inc(v_fvarId_418_);
lean_dec_ref_known(v_subExpr_401_, 1);
v___x_419_ = lean_st_ref_take(v___y_402_);
v___x_420_ = l_Lean_FVarIdSet_insert(v___x_419_, v_fvarId_418_);
v___x_421_ = lean_st_ref_put(v___y_402_, v___x_420_);
if (v_isShared_416_ == 0)
{
v___x_423_ = v___x_415_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_413_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v_a_413_);
lean_dec_ref(v_subExpr_401_);
v___x_425_ = lean_box(v___x_408_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_425_);
v___x_427_ = v___x_415_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec(v_a_413_);
lean_dec_ref(v_subExpr_401_);
v___x_429_ = lean_box(v___x_411_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_429_);
v___x_431_ = v___x_415_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
lean_dec_ref(v_subExpr_401_);
return v___x_412_;
}
}
else
{
uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v_subExpr_401_);
v___x_434_ = 0;
v___x_435_ = lean_box(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0___boxed(lean_object* v_subExpr_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(v_subExpr_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_object* v_00_u03b1_445_, lean_object* v_x_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_apply_1(v_x_446_, lean_box(0));
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_455_, lean_object* v_x_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(v_00_u03b1_455_, v_x_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
lean_inc(v___y_466_);
lean_inc(v___y_465_);
v___x_473_ = lean_apply_8(v_k_464_, v_b_467_, v___y_465_, v___y_466_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, lean_box(0));
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(v_k_474_, v___y_475_, v___y_476_, v_b_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_476_);
lean_dec(v___y_475_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_name_484_, uint8_t v_bi_485_, lean_object* v_type_486_, lean_object* v_k_487_, uint8_t v_kind_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___f_496_; lean_object* v___x_497_; 
lean_inc(v___y_490_);
lean_inc(v___y_489_);
v___f_496_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_496_, 0, v_k_487_);
lean_closure_set(v___f_496_, 1, v___y_489_);
lean_closure_set(v___f_496_, 2, v___y_490_);
v___x_497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_484_, v_bi_485_, v_type_486_, v___f_496_, v_kind_488_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_497_) == 0)
{
return v___x_497_;
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_506_, lean_object* v_bi_507_, lean_object* v_type_508_, lean_object* v_k_509_, lean_object* v_kind_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v_bi_boxed_518_; uint8_t v_kind_boxed_519_; lean_object* v_res_520_; 
v_bi_boxed_518_ = lean_unbox(v_bi_507_);
v_kind_boxed_519_ = lean_unbox(v_kind_510_);
v_res_520_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_506_, v_bi_boxed_518_, v_type_508_, v_k_509_, v_kind_boxed_519_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___y_511_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_521_, lean_object* v_f_522_, lean_object* v_body_523_, lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(v_fvars_521_, v_f_522_, v_body_523_, v_x_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec(v___y_525_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(lean_object* v_f_533_, lean_object* v_fvars_534_, lean_object* v_a_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
if (lean_obj_tag(v_a_535_) == 7)
{
lean_object* v_binderName_543_; lean_object* v_binderType_544_; lean_object* v_body_545_; uint8_t v_binderInfo_546_; lean_object* v___f_547_; lean_object* v_d_548_; lean_object* v___x_549_; 
v_binderName_543_ = lean_ctor_get(v_a_535_, 0);
lean_inc(v_binderName_543_);
v_binderType_544_ = lean_ctor_get(v_a_535_, 1);
lean_inc_ref(v_binderType_544_);
v_body_545_ = lean_ctor_get(v_a_535_, 2);
lean_inc_ref(v_body_545_);
v_binderInfo_546_ = lean_ctor_get_uint8(v_a_535_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_535_, 3);
lean_inc_ref(v_f_533_);
lean_inc_ref(v_fvars_534_);
v___f_547_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed), 11, 3);
lean_closure_set(v___f_547_, 0, v_fvars_534_);
lean_closure_set(v___f_547_, 1, v_f_533_);
lean_closure_set(v___f_547_, 2, v_body_545_);
v_d_548_ = lean_expr_instantiate_rev(v_binderType_544_, v_fvars_534_);
lean_dec_ref(v_fvars_534_);
lean_dec_ref(v_binderType_544_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v_d_548_);
v___x_549_ = lean_apply_8(v_f_533_, v_d_548_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, lean_box(0));
if (lean_obj_tag(v___x_549_) == 0)
{
uint8_t v___x_550_; lean_object* v___x_551_; 
lean_dec_ref_known(v___x_549_, 1);
v___x_550_ = 0;
v___x_551_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_543_, v_binderInfo_546_, v_d_548_, v___f_547_, v___x_550_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
return v___x_551_;
}
else
{
lean_dec_ref(v_d_548_);
lean_dec_ref(v___f_547_);
lean_dec(v_binderName_543_);
return v___x_549_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_expr_instantiate_rev(v_a_535_, v_fvars_534_);
lean_dec_ref(v_fvars_534_);
lean_dec_ref(v_a_535_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc(v___y_537_);
lean_inc(v___y_536_);
v___x_553_ = lean_apply_8(v_f_533_, v___x_552_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, lean_box(0));
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(lean_object* v_fvars_554_, lean_object* v_f_555_, lean_object* v_body_556_, lean_object* v_x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_array_push(v_fvars_554_, v_x_557_);
v___x_566_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_555_, v___x_565_, v_body_556_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_f_567_, lean_object* v_fvars_568_, lean_object* v_a_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_567_, v_fvars_568_, v_a_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec(v___y_570_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(lean_object* v_f_580_, lean_object* v_e_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_590_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_580_, v___x_589_, v_e_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___boxed(lean_object* v_f_591_, lean_object* v_e_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v_f_591_, v_e_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec(v___y_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
return v_x_601_;
}
else
{
lean_object* v_key_603_; lean_object* v_value_604_; lean_object* v_tail_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_628_; 
v_key_603_ = lean_ctor_get(v_x_602_, 0);
v_value_604_ = lean_ctor_get(v_x_602_, 1);
v_tail_605_ = lean_ctor_get(v_x_602_, 2);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_628_ == 0)
{
v___x_607_ = v_x_602_;
v_isShared_608_ = v_isSharedCheck_628_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_tail_605_);
lean_inc(v_value_604_);
lean_inc(v_key_603_);
lean_dec(v_x_602_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_628_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v___x_612_; uint64_t v_fold_613_; uint64_t v___x_614_; uint64_t v___x_615_; uint64_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_609_ = lean_array_get_size(v_x_601_);
v___x_610_ = l_Lean_Expr_hash(v_key_603_);
v___x_611_ = 32ULL;
v___x_612_ = lean_uint64_shift_right(v___x_610_, v___x_611_);
v_fold_613_ = lean_uint64_xor(v___x_610_, v___x_612_);
v___x_614_ = 16ULL;
v___x_615_ = lean_uint64_shift_right(v_fold_613_, v___x_614_);
v___x_616_ = lean_uint64_xor(v_fold_613_, v___x_615_);
v___x_617_ = lean_uint64_to_usize(v___x_616_);
v___x_618_ = lean_usize_of_nat(v___x_609_);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_sub(v___x_618_, v___x_619_);
v___x_621_ = lean_usize_land(v___x_617_, v___x_620_);
v___x_622_ = lean_array_uget_borrowed(v_x_601_, v___x_621_);
lean_inc(v___x_622_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 2, v___x_622_);
v___x_624_ = v___x_607_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_key_603_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_value_604_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v___x_622_);
v___x_624_ = v_reuseFailAlloc_627_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; 
v___x_625_ = lean_array_uset(v_x_601_, v___x_621_, v___x_624_);
v_x_601_ = v___x_625_;
v_x_602_ = v_tail_605_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_i_629_, lean_object* v_source_630_, lean_object* v_target_631_){
_start:
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = lean_array_get_size(v_source_630_);
v___x_633_ = lean_nat_dec_lt(v_i_629_, v___x_632_);
if (v___x_633_ == 0)
{
lean_dec_ref(v_source_630_);
lean_dec(v_i_629_);
return v_target_631_;
}
else
{
lean_object* v_es_634_; lean_object* v___x_635_; lean_object* v_source_636_; lean_object* v_target_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_es_634_ = lean_array_fget(v_source_630_, v_i_629_);
v___x_635_ = lean_box(0);
v_source_636_ = lean_array_fset(v_source_630_, v_i_629_, v___x_635_);
v_target_637_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_target_631_, v_es_634_);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_i_629_, v___x_638_);
lean_dec(v_i_629_);
v_i_629_ = v___x_639_;
v_source_630_ = v_source_636_;
v_target_631_ = v_target_637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_data_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_nbuckets_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_642_ = lean_array_get_size(v_data_641_);
v___x_643_ = lean_unsigned_to_nat(2u);
v_nbuckets_644_ = lean_nat_mul(v___x_642_, v___x_643_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_box(0);
v___x_647_ = lean_mk_array(v_nbuckets_644_, v___x_646_);
v___x_648_ = lean_array_propagate_mark(v_data_641_, v___x_647_);
v___x_649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v___x_645_, v_data_641_, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_a_650_, lean_object* v_b_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_dec(v_b_651_);
lean_dec_ref(v_a_650_);
return v_x_652_;
}
else
{
lean_object* v_key_653_; lean_object* v_value_654_; lean_object* v_tail_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_667_; 
v_key_653_ = lean_ctor_get(v_x_652_, 0);
v_value_654_ = lean_ctor_get(v_x_652_, 1);
v_tail_655_ = lean_ctor_get(v_x_652_, 2);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_667_ == 0)
{
v___x_657_ = v_x_652_;
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_tail_655_);
lean_inc(v_value_654_);
lean_inc(v_key_653_);
lean_dec(v_x_652_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; 
v___x_659_ = lean_expr_eqv(v_key_653_, v_a_650_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_650_, v_b_651_, v_tail_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 2, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_key_653_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_value_654_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v___x_665_; 
lean_dec(v_value_654_);
lean_dec(v_key_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_b_651_);
lean_ctor_set(v___x_657_, 0, v_a_650_);
v___x_665_ = v___x_657_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_650_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_b_651_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_tail_655_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_a_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
uint8_t v___x_670_; 
v___x_670_ = 0;
return v___x_670_;
}
else
{
lean_object* v_key_671_; lean_object* v_tail_672_; uint8_t v___x_673_; 
v_key_671_ = lean_ctor_get(v_x_669_, 0);
v_tail_672_ = lean_ctor_get(v_x_669_, 2);
v___x_673_ = lean_expr_eqv(v_key_671_, v_a_668_);
if (v___x_673_ == 0)
{
v_x_669_ = v_tail_672_;
goto _start;
}
else
{
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_675_, v_x_676_);
lean_dec(v_x_676_);
lean_dec_ref(v_a_675_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(lean_object* v_m_679_, lean_object* v_a_680_, lean_object* v_b_681_){
_start:
{
lean_object* v_size_682_; lean_object* v_buckets_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_726_; 
v_size_682_ = lean_ctor_get(v_m_679_, 0);
v_buckets_683_ = lean_ctor_get(v_m_679_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_m_679_);
if (v_isSharedCheck_726_ == 0)
{
v___x_685_ = v_m_679_;
v_isShared_686_ = v_isSharedCheck_726_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_buckets_683_);
lean_inc(v_size_682_);
lean_dec(v_m_679_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_726_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; uint64_t v_fold_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v_bkt_700_; uint8_t v___x_701_; 
v___x_687_ = lean_array_get_size(v_buckets_683_);
v___x_688_ = l_Lean_Expr_hash(v_a_680_);
v___x_689_ = 32ULL;
v___x_690_ = lean_uint64_shift_right(v___x_688_, v___x_689_);
v_fold_691_ = lean_uint64_xor(v___x_688_, v___x_690_);
v___x_692_ = 16ULL;
v___x_693_ = lean_uint64_shift_right(v_fold_691_, v___x_692_);
v___x_694_ = lean_uint64_xor(v_fold_691_, v___x_693_);
v___x_695_ = lean_uint64_to_usize(v___x_694_);
v___x_696_ = lean_usize_of_nat(v___x_687_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_sub(v___x_696_, v___x_697_);
v___x_699_ = lean_usize_land(v___x_695_, v___x_698_);
v_bkt_700_ = lean_array_uget_borrowed(v_buckets_683_, v___x_699_);
v___x_701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_680_, v_bkt_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v_size_x27_703_; lean_object* v___x_704_; lean_object* v_buckets_x27_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_702_ = lean_unsigned_to_nat(1u);
v_size_x27_703_ = lean_nat_add(v_size_682_, v___x_702_);
lean_dec(v_size_682_);
lean_inc(v_bkt_700_);
v___x_704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_704_, 0, v_a_680_);
lean_ctor_set(v___x_704_, 1, v_b_681_);
lean_ctor_set(v___x_704_, 2, v_bkt_700_);
v_buckets_x27_705_ = lean_array_uset(v_buckets_683_, v___x_699_, v___x_704_);
v___x_706_ = lean_unsigned_to_nat(4u);
v___x_707_ = lean_nat_mul(v_size_x27_703_, v___x_706_);
v___x_708_ = lean_unsigned_to_nat(3u);
v___x_709_ = lean_nat_div(v___x_707_, v___x_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_array_get_size(v_buckets_x27_705_);
v___x_711_ = lean_nat_dec_le(v___x_709_, v___x_710_);
lean_dec(v___x_709_);
if (v___x_711_ == 0)
{
lean_object* v_val_712_; lean_object* v___x_714_; 
v_val_712_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_buckets_x27_705_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_val_712_);
lean_ctor_set(v___x_685_, 0, v_size_x27_703_);
v___x_714_ = v___x_685_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_size_x27_703_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_val_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_object* v___x_717_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_buckets_x27_705_);
lean_ctor_set(v___x_685_, 0, v_size_x27_703_);
v___x_717_ = v___x_685_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_size_x27_703_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_buckets_x27_705_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v___x_719_; lean_object* v_buckets_x27_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_inc(v_bkt_700_);
v___x_719_ = lean_box(0);
v_buckets_x27_720_ = lean_array_uset(v_buckets_683_, v___x_699_, v___x_719_);
v___x_721_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_680_, v_b_681_, v_bkt_700_);
v___x_722_ = lean_array_uset(v_buckets_x27_720_, v___x_699_, v___x_721_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_722_);
v___x_724_ = v___x_685_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_size_682_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(lean_object* v_a_727_, lean_object* v_e_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_st_ref_take(v_a_727_);
v___x_732_ = lean_box(0);
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v___x_731_, v_e_728_, v_a_729_);
v___x_734_ = lean_st_ref_put(v_a_727_, v___x_733_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed(lean_object* v_a_735_, lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(v_a_735_, v_e_736_, v_a_737_);
lean_dec(v_a_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(lean_object* v_name_740_, lean_object* v_type_741_, lean_object* v_val_742_, lean_object* v_k_743_, uint8_t v_nondep_744_, uint8_t v_kind_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; 
lean_inc(v___y_747_);
lean_inc(v___y_746_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_753_, 0, v_k_743_);
lean_closure_set(v___f_753_, 1, v___y_746_);
lean_closure_set(v___f_753_, 2, v___y_747_);
v___x_754_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_740_, v_type_741_, v_val_742_, v___f_753_, v_nondep_744_, v_kind_745_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_754_) == 0)
{
return v___x_754_;
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg___boxed(lean_object* v_name_763_, lean_object* v_type_764_, lean_object* v_val_765_, lean_object* v_k_766_, lean_object* v_nondep_767_, lean_object* v_kind_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v_nondep_boxed_776_; uint8_t v_kind_boxed_777_; lean_object* v_res_778_; 
v_nondep_boxed_776_ = lean_unbox(v_nondep_767_);
v_kind_boxed_777_ = lean_unbox(v_kind_768_);
v_res_778_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_763_, v_type_764_, v_val_765_, v_k_766_, v_nondep_boxed_776_, v_kind_boxed_777_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec(v___y_769_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed(lean_object* v_fvars_779_, lean_object* v_f_780_, lean_object* v_body_781_, lean_object* v_x_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(v_fvars_779_, v_f_780_, v_body_781_, v_x_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v___y_783_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(lean_object* v_f_791_, lean_object* v_fvars_792_, lean_object* v_a_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
if (lean_obj_tag(v_a_793_) == 8)
{
lean_object* v_declName_801_; lean_object* v_type_802_; lean_object* v_value_803_; lean_object* v_body_804_; lean_object* v___f_805_; lean_object* v_d_806_; lean_object* v_v_807_; lean_object* v___x_808_; 
v_declName_801_ = lean_ctor_get(v_a_793_, 0);
lean_inc(v_declName_801_);
v_type_802_ = lean_ctor_get(v_a_793_, 1);
lean_inc_ref(v_type_802_);
v_value_803_ = lean_ctor_get(v_a_793_, 2);
lean_inc_ref(v_value_803_);
v_body_804_ = lean_ctor_get(v_a_793_, 3);
lean_inc_ref(v_body_804_);
lean_dec_ref_known(v_a_793_, 4);
lean_inc_ref_n(v_f_791_, 2);
lean_inc_ref(v_fvars_792_);
v___f_805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed), 11, 3);
lean_closure_set(v___f_805_, 0, v_fvars_792_);
lean_closure_set(v___f_805_, 1, v_f_791_);
lean_closure_set(v___f_805_, 2, v_body_804_);
v_d_806_ = lean_expr_instantiate_rev(v_type_802_, v_fvars_792_);
lean_dec_ref(v_type_802_);
v_v_807_ = lean_expr_instantiate_rev(v_value_803_, v_fvars_792_);
lean_dec_ref(v_fvars_792_);
lean_dec_ref(v_value_803_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v_d_806_);
v___x_808_ = lean_apply_8(v_f_791_, v_d_806_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, lean_box(0));
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v___x_809_; 
lean_dec_ref_known(v___x_808_, 1);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v_v_807_);
v___x_809_ = lean_apply_8(v_f_791_, v_v_807_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, lean_box(0));
if (lean_obj_tag(v___x_809_) == 0)
{
uint8_t v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; 
lean_dec_ref_known(v___x_809_, 1);
v___x_810_ = 0;
v___x_811_ = 0;
v___x_812_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_declName_801_, v_d_806_, v_v_807_, v___f_805_, v___x_810_, v___x_811_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_812_;
}
else
{
lean_dec_ref(v_v_807_);
lean_dec_ref(v_d_806_);
lean_dec_ref(v___f_805_);
lean_dec(v_declName_801_);
return v___x_809_;
}
}
else
{
lean_dec_ref(v_v_807_);
lean_dec_ref(v_d_806_);
lean_dec_ref(v___f_805_);
lean_dec(v_declName_801_);
lean_dec_ref(v_f_791_);
return v___x_808_;
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_expr_instantiate_rev(v_a_793_, v_fvars_792_);
lean_dec_ref(v_fvars_792_);
lean_dec_ref(v_a_793_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v___y_795_);
lean_inc(v___y_794_);
v___x_814_ = lean_apply_8(v_f_791_, v___x_813_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, lean_box(0));
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(lean_object* v_fvars_815_, lean_object* v_f_816_, lean_object* v_body_817_, lean_object* v_x_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_array_push(v_fvars_815_, v_x_818_);
v___x_827_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_816_, v___x_826_, v_body_817_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___boxed(lean_object* v_f_828_, lean_object* v_fvars_829_, lean_object* v_a_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_828_, v_fvars_829_, v_a_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(lean_object* v_f_839_, lean_object* v_e_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_849_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_839_, v___x_848_, v_e_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5___boxed(lean_object* v_f_850_, lean_object* v_e_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v_f_850_, v_e_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec(v___y_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_860_, lean_object* v_f_861_, lean_object* v_body_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(v_fvars_860_, v_f_861_, v_body_862_, v_x_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(lean_object* v_f_872_, lean_object* v_fvars_873_, lean_object* v_a_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
if (lean_obj_tag(v_a_874_) == 6)
{
lean_object* v_binderName_882_; lean_object* v_binderType_883_; lean_object* v_body_884_; uint8_t v_binderInfo_885_; lean_object* v___f_886_; lean_object* v_d_887_; lean_object* v___x_888_; 
v_binderName_882_ = lean_ctor_get(v_a_874_, 0);
lean_inc(v_binderName_882_);
v_binderType_883_ = lean_ctor_get(v_a_874_, 1);
lean_inc_ref(v_binderType_883_);
v_body_884_ = lean_ctor_get(v_a_874_, 2);
lean_inc_ref(v_body_884_);
v_binderInfo_885_ = lean_ctor_get_uint8(v_a_874_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_874_, 3);
lean_inc_ref(v_f_872_);
lean_inc_ref(v_fvars_873_);
v___f_886_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed), 11, 3);
lean_closure_set(v___f_886_, 0, v_fvars_873_);
lean_closure_set(v___f_886_, 1, v_f_872_);
lean_closure_set(v___f_886_, 2, v_body_884_);
v_d_887_ = lean_expr_instantiate_rev(v_binderType_883_, v_fvars_873_);
lean_dec_ref(v_fvars_873_);
lean_dec_ref(v_binderType_883_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v_d_887_);
v___x_888_ = lean_apply_8(v_f_872_, v_d_887_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
if (lean_obj_tag(v___x_888_) == 0)
{
uint8_t v___x_889_; lean_object* v___x_890_; 
lean_dec_ref_known(v___x_888_, 1);
v___x_889_ = 0;
v___x_890_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_882_, v_binderInfo_885_, v_d_887_, v___f_886_, v___x_889_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
return v___x_890_;
}
else
{
lean_dec_ref(v_d_887_);
lean_dec_ref(v___f_886_);
lean_dec(v_binderName_882_);
return v___x_888_;
}
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = lean_expr_instantiate_rev(v_a_874_, v_fvars_873_);
lean_dec_ref(v_fvars_873_);
lean_dec_ref(v_a_874_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc(v___y_876_);
lean_inc(v___y_875_);
v___x_892_ = lean_apply_8(v_f_872_, v___x_891_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, lean_box(0));
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(lean_object* v_fvars_893_, lean_object* v_f_894_, lean_object* v_body_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_array_push(v_fvars_893_, v_x_896_);
v___x_905_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_894_, v___x_904_, v_body_895_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_f_906_, lean_object* v_fvars_907_, lean_object* v_a_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_906_, v_fvars_907_, v_a_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec(v___y_909_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(lean_object* v_f_917_, lean_object* v_e_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_927_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_917_, v___x_926_, v_e_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4___boxed(lean_object* v_f_928_, lean_object* v_e_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v_f_928_, v_e_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec(v___y_930_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_938_, lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_box(0);
return v___x_940_;
}
else
{
lean_object* v_key_941_; lean_object* v_value_942_; lean_object* v_tail_943_; uint8_t v___x_944_; 
v_key_941_ = lean_ctor_get(v_x_939_, 0);
v_value_942_ = lean_ctor_get(v_x_939_, 1);
v_tail_943_ = lean_ctor_get(v_x_939_, 2);
v___x_944_ = lean_expr_eqv(v_key_941_, v_a_938_);
if (v___x_944_ == 0)
{
v_x_939_ = v_tail_943_;
goto _start;
}
else
{
lean_object* v___x_946_; 
lean_inc(v_value_942_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v_value_942_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_947_, lean_object* v_x_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_947_, v_x_948_);
lean_dec(v_x_948_);
lean_dec_ref(v_a_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(lean_object* v_m_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_buckets_952_; lean_object* v___x_953_; uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v___x_956_; uint64_t v_fold_957_; uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_buckets_952_ = lean_ctor_get(v_m_950_, 1);
v___x_953_ = lean_array_get_size(v_buckets_952_);
v___x_954_ = l_Lean_Expr_hash(v_a_951_);
v___x_955_ = 32ULL;
v___x_956_ = lean_uint64_shift_right(v___x_954_, v___x_955_);
v_fold_957_ = lean_uint64_xor(v___x_954_, v___x_956_);
v___x_958_ = 16ULL;
v___x_959_ = lean_uint64_shift_right(v_fold_957_, v___x_958_);
v___x_960_ = lean_uint64_xor(v_fold_957_, v___x_959_);
v___x_961_ = lean_uint64_to_usize(v___x_960_);
v___x_962_ = lean_usize_of_nat(v___x_953_);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_sub(v___x_962_, v___x_963_);
v___x_965_ = lean_usize_land(v___x_961_, v___x_964_);
v___x_966_ = lean_array_uget_borrowed(v_buckets_952_, v___x_965_);
v___x_967_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_951_, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_968_, v_a_969_);
lean_dec_ref(v_a_969_);
lean_dec_ref(v_m_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_apply_1(v_x_972_, lean_box(0));
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(v_00_u03b1_981_, v_x_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed(lean_object* v_fn_990_, lean_object* v_e_991_, lean_object* v_a_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_990_, v_e_991_, v_a_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec(v_a_992_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(lean_object* v_fn_1000_, lean_object* v_e_1001_, lean_object* v_a_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_a_1010_; lean_object* v___y_1022_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_inc(v_a_1002_);
v___x_1024_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1024_, 0, lean_box(0));
lean_closure_set(v___x_1024_, 1, lean_box(0));
lean_closure_set(v___x_1024_, 2, v_a_1002_);
v___x_1025_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_box(0), v___x_1024_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1062_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1062_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1062_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_a_1026_, v_e_1001_);
lean_dec(v_a_1026_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; 
lean_del_object(v___x_1028_);
lean_inc_ref(v_fn_1000_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc_ref(v_e_1001_);
v___x_1031_ = lean_apply_7(v_fn_1000_, v_e_1001_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; uint8_t v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = lean_unbox(v_a_1032_);
lean_dec(v_a_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref(v_fn_1000_);
v___x_1034_ = lean_box(0);
v_a_1010_ = v___x_1034_;
goto v___jp_1009_;
}
else
{
switch(lean_obj_tag(v_e_1001_))
{
case 7:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1035_, 0, v_fn_1000_);
lean_inc_ref(v_e_1001_);
v___x_1036_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v___x_1035_, v_e_1001_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
v___y_1022_ = v___x_1036_;
goto v___jp_1021_;
}
case 6:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1037_, 0, v_fn_1000_);
lean_inc_ref(v_e_1001_);
v___x_1038_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v___x_1037_, v_e_1001_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
v___y_1022_ = v___x_1038_;
goto v___jp_1021_;
}
case 8:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1039_, 0, v_fn_1000_);
lean_inc_ref(v_e_1001_);
v___x_1040_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v___x_1039_, v_e_1001_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
v___y_1022_ = v___x_1040_;
goto v___jp_1021_;
}
case 5:
{
lean_object* v_fn_1041_; lean_object* v_arg_1042_; lean_object* v___x_1043_; 
v_fn_1041_ = lean_ctor_get(v_e_1001_, 0);
v_arg_1042_ = lean_ctor_get(v_e_1001_, 1);
lean_inc_ref(v_fn_1041_);
lean_inc_ref(v_fn_1000_);
v___x_1043_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1000_, v_fn_1041_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; 
lean_dec_ref_known(v___x_1043_, 1);
lean_inc_ref(v_arg_1042_);
v___x_1044_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1000_, v_arg_1042_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
v___y_1022_ = v___x_1044_;
goto v___jp_1021_;
}
else
{
lean_dec_ref_known(v_e_1001_, 2);
lean_dec_ref(v_fn_1000_);
return v___x_1043_;
}
}
case 10:
{
lean_object* v_expr_1045_; lean_object* v___x_1046_; 
v_expr_1045_ = lean_ctor_get(v_e_1001_, 1);
lean_inc_ref(v_expr_1045_);
v___x_1046_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1000_, v_expr_1045_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
v___y_1022_ = v___x_1046_;
goto v___jp_1021_;
}
case 11:
{
lean_object* v_struct_1047_; lean_object* v___x_1048_; 
v_struct_1047_ = lean_ctor_get(v_e_1001_, 2);
lean_inc_ref(v_struct_1047_);
v___x_1048_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1000_, v_struct_1047_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
v___y_1022_ = v___x_1048_;
goto v___jp_1021_;
}
default: 
{
lean_object* v___x_1049_; 
lean_dec_ref(v_fn_1000_);
v___x_1049_ = lean_box(0);
v_a_1010_ = v___x_1049_;
goto v___jp_1009_;
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_e_1001_);
lean_dec_ref(v_fn_1000_);
v_a_1050_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1031_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1031_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
else
{
lean_object* v_val_1058_; lean_object* v___x_1060_; 
lean_dec_ref(v_e_1001_);
lean_dec_ref(v_fn_1000_);
v_val_1058_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1030_, 1);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v_val_1058_);
v___x_1060_ = v___x_1028_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_val_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_e_1001_);
lean_dec_ref(v_fn_1000_);
v_a_1063_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1025_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1025_);
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
v___jp_1009_:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; 
lean_inc(v_a_1002_);
v___f_1011_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1011_, 0, v_a_1002_);
lean_closure_set(v___f_1011_, 1, v_e_1001_);
lean_closure_set(v___f_1011_, 2, v_a_1010_);
v___x_1012_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_box(0), v___f_1011_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v___x_1012_, 0);
lean_dec(v_unused_1020_);
v___x_1014_ = v___x_1012_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_dec(v___x_1012_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_a_1010_);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1010_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
return v___x_1012_;
}
}
v___jp_1021_:
{
if (lean_obj_tag(v___y_1022_) == 0)
{
lean_object* v_a_1023_; 
v_a_1023_ = lean_ctor_get(v___y_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___y_1022_, 1);
v_a_1010_ = v_a_1023_;
goto v___jp_1009_;
}
else
{
lean_dec_ref(v_e_1001_);
return v___y_1022_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_unsigned_to_nat(16u);
v___x_1073_ = lean_mk_array(v___x_1072_, v___x_1071_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1);
v___x_1078_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1078_, 0, lean_box(0));
lean_closure_set(v___x_1078_, 1, lean_box(0));
lean_closure_set(v___x_1078_, 2, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(lean_object* v_input_1079_, lean_object* v_fn_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_a_1089_; lean_object* v___x_1090_; 
v___x_1087_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2);
v___x_1088_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_box(0), v___x_1087_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v___x_1088_);
v___x_1090_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1080_, v_input_1079_, v_a_1089_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1092_, 0, lean_box(0));
lean_closure_set(v___x_1092_, 1, lean_box(0));
lean_closure_set(v___x_1092_, 2, v_a_1089_);
v___x_1093_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_box(0), v___x_1092_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1093_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___x_1093_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_a_1091_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1091_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_dec(v_a_1089_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___boxed(lean_object* v_input_1102_, lean_object* v_fn_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_input_1102_, v_fn_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(lean_object* v_e_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; 
v___f_1119_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0));
v___x_1120_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_e_1112_, v___f_1119_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___boxed(lean_object* v_e_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1129_, lean_object* v_m_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_1130_, v_a_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1133_, lean_object* v_m_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(v_00_u03b2_1133_, v_m_1134_, v_a_1135_);
lean_dec_ref(v_a_1135_);
lean_dec_ref(v_m_1134_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1137_, lean_object* v_m_1138_, lean_object* v_a_1139_, lean_object* v_b_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v_m_1138_, v_a_1139_, v_b_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1142_, lean_object* v_a_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1143_, v_x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1146_, lean_object* v_a_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1146_, v_a_1147_, v_x_1148_);
lean_dec(v_x_1148_);
lean_dec_ref(v_a_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1150_, lean_object* v_a_1151_, lean_object* v_x_1152_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_1151_, v_x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_a_1155_, lean_object* v_x_1156_){
_start:
{
uint8_t v_res_1157_; lean_object* v_r_1158_; 
v_res_1157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1154_, v_a_1155_, v_x_1156_);
lean_dec(v_x_1156_);
lean_dec_ref(v_a_1155_);
v_r_1158_ = lean_box(v_res_1157_);
return v_r_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1159_, lean_object* v_data_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_data_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1162_, lean_object* v_a_1163_, lean_object* v_b_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_1163_, v_b_1164_, v_x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_1167_, lean_object* v_name_1168_, uint8_t v_bi_1169_, lean_object* v_type_1170_, lean_object* v_k_1171_, uint8_t v_kind_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_1168_, v_bi_1169_, v_type_1170_, v_k_1171_, v_kind_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_name_1182_, lean_object* v_bi_1183_, lean_object* v_type_1184_, lean_object* v_k_1185_, lean_object* v_kind_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
uint8_t v_bi_boxed_1194_; uint8_t v_kind_boxed_1195_; lean_object* v_res_1196_; 
v_bi_boxed_1194_ = lean_unbox(v_bi_1183_);
v_kind_boxed_1195_ = lean_unbox(v_kind_1186_);
v_res_1196_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_1181_, v_name_1182_, v_bi_boxed_1194_, v_type_1184_, v_k_1185_, v_kind_boxed_1195_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(lean_object* v_00_u03b1_1197_, lean_object* v_name_1198_, lean_object* v_type_1199_, lean_object* v_val_1200_, lean_object* v_k_1201_, uint8_t v_nondep_1202_, uint8_t v_kind_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_1198_, v_type_1199_, v_val_1200_, v_k_1201_, v_nondep_1202_, v_kind_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1212_, lean_object* v_name_1213_, lean_object* v_type_1214_, lean_object* v_val_1215_, lean_object* v_k_1216_, lean_object* v_nondep_1217_, lean_object* v_kind_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
uint8_t v_nondep_boxed_1226_; uint8_t v_kind_boxed_1227_; lean_object* v_res_1228_; 
v_nondep_boxed_1226_ = lean_unbox(v_nondep_1217_);
v_kind_boxed_1227_ = lean_unbox(v_kind_1218_);
v_res_1228_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(v_00_u03b1_1212_, v_name_1213_, v_type_1214_, v_val_1215_, v_k_1216_, v_nondep_boxed_1226_, v_kind_boxed_1227_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1229_, lean_object* v_i_1230_, lean_object* v_source_1231_, lean_object* v_target_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_i_1230_, v_source_1231_, v_target_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10(lean_object* v_00_u03b2_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_x_1235_, v_x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(lean_object* v_k_1238_, lean_object* v___y_1239_, lean_object* v_b_1240_, lean_object* v_c_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v___y_1242_);
lean_inc(v___y_1239_);
v___x_1247_ = lean_apply_8(v_k_1238_, v_b_1240_, v_c_1241_, v___y_1239_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, lean_box(0));
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_1248_, lean_object* v___y_1249_, lean_object* v_b_1250_, lean_object* v_c_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(v_k_1248_, v___y_1249_, v_b_1250_, v_c_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1249_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(lean_object* v_type_1258_, lean_object* v_maxFVars_x3f_1259_, lean_object* v_k_1260_, uint8_t v_cleanupAnnotations_1261_, uint8_t v_whnfType_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___f_1269_; lean_object* v___x_1270_; 
lean_inc(v___y_1263_);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1269_, 0, v_k_1260_);
lean_closure_set(v___f_1269_, 1, v___y_1263_);
v___x_1270_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1258_, v_maxFVars_x3f_1259_, v___f_1269_, v_cleanupAnnotations_1261_, v_whnfType_1262_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1270_) == 0)
{
return v___x_1270_;
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___boxed(lean_object* v_type_1279_, lean_object* v_maxFVars_x3f_1280_, lean_object* v_k_1281_, lean_object* v_cleanupAnnotations_1282_, lean_object* v_whnfType_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1290_; uint8_t v_whnfType_boxed_1291_; lean_object* v_res_1292_; 
v_cleanupAnnotations_boxed_1290_ = lean_unbox(v_cleanupAnnotations_1282_);
v_whnfType_boxed_1291_ = lean_unbox(v_whnfType_1283_);
v_res_1292_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_1279_, v_maxFVars_x3f_1280_, v_k_1281_, v_cleanupAnnotations_boxed_1290_, v_whnfType_boxed_1291_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(lean_object* v_00_u03b1_1293_, lean_object* v_type_1294_, lean_object* v_maxFVars_x3f_1295_, lean_object* v_k_1296_, uint8_t v_cleanupAnnotations_1297_, uint8_t v_whnfType_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_1294_, v_maxFVars_x3f_1295_, v_k_1296_, v_cleanupAnnotations_1297_, v_whnfType_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_type_1307_, lean_object* v_maxFVars_x3f_1308_, lean_object* v_k_1309_, lean_object* v_cleanupAnnotations_1310_, lean_object* v_whnfType_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1318_; uint8_t v_whnfType_boxed_1319_; lean_object* v_res_1320_; 
v_cleanupAnnotations_boxed_1318_ = lean_unbox(v_cleanupAnnotations_1310_);
v_whnfType_boxed_1319_ = lean_unbox(v_whnfType_1311_);
v_res_1320_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(v_00_u03b1_1306_, v_type_1307_, v_maxFVars_x3f_1308_, v_k_1309_, v_cleanupAnnotations_boxed_1318_, v_whnfType_boxed_1319_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed(lean_object* v___x_1321_, lean_object* v_currentBinderIdx_1322_, lean_object* v___x_1323_, lean_object* v_currentFVars_1324_, lean_object* v_p_1325_, lean_object* v_fvar_1326_, lean_object* v_e_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(v___x_1321_, v_currentBinderIdx_1322_, v___x_1323_, v_currentFVars_1324_, v_p_1325_, v_fvar_1326_, v_e_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v_fvar_1326_);
lean_dec(v___x_1323_);
lean_dec_ref(v___x_1321_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(lean_object* v_p_1337_, lean_object* v_e_1338_, lean_object* v_currentBinderIdx_1339_, lean_object* v_currentFVars_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_e_1347_; uint8_t v___x_1348_; 
v_e_1347_ = l_Lean_Expr_cleanupAnnotations(v_e_1338_);
v___x_1348_ = l_Lean_Expr_isForall(v_e_1347_);
if (v___x_1348_ == 0)
{
if (lean_obj_tag(v_e_1347_) == 8)
{
lean_object* v_type_1349_; lean_object* v_body_1350_; lean_object* v___x_1351_; 
v_type_1349_ = lean_ctor_get(v_e_1347_, 1);
lean_inc_ref_n(v_type_1349_, 2);
v_body_1350_ = lean_ctor_get(v_e_1347_, 3);
lean_inc_ref(v_body_1350_);
lean_dec_ref_known(v_e_1347_, 4);
v___x_1351_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_type_1349_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v___x_1352_; 
lean_dec_ref_known(v___x_1351_, 1);
v___x_1352_ = l_Lean_Meta_mkSorry(v_type_1349_, v___x_1348_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = lean_expr_instantiate1(v_body_1350_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_body_1350_);
v_e_1338_ = v___x_1354_;
goto _start;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v_body_1350_);
lean_dec_ref(v_currentFVars_1340_);
lean_dec(v_currentBinderIdx_1339_);
lean_dec_ref(v_p_1337_);
v_a_1356_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1352_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1352_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v_body_1350_);
lean_dec_ref(v_type_1349_);
lean_dec_ref(v_currentFVars_1340_);
lean_dec(v_currentBinderIdx_1339_);
lean_dec_ref(v_p_1337_);
v_a_1364_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1351_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1351_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v___x_1372_; 
lean_dec(v_currentBinderIdx_1339_);
lean_dec_ref(v_p_1337_);
v___x_1372_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_1347_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1372_, 0);
lean_dec(v_unused_1380_);
v___x_1374_ = v___x_1372_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v___x_1372_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v_currentFVars_1340_);
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_currentFVars_1340_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_currentFVars_1340_);
v_a_1381_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1372_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1372_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
else
{
lean_object* v_binderType_1389_; lean_object* v_body_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_binderType_1389_ = lean_ctor_get(v_e_1347_, 1);
v_body_1390_ = lean_ctor_get(v_e_1347_, 2);
v___x_1391_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_binderType_1389_);
v___x_1392_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_binderType_1389_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1392_) == 0)
{
uint8_t v___y_1394_; uint8_t v___x_1409_; uint8_t v___x_1410_; 
lean_dec_ref_known(v___x_1392_, 1);
v___x_1409_ = l_Lean_Expr_binderInfo(v_e_1347_);
v___x_1410_ = l_Lean_BinderInfo_isInstImplicit(v___x_1409_);
if (v___x_1410_ == 0)
{
lean_inc_ref(v_body_1390_);
lean_inc_ref(v_binderType_1389_);
lean_dec_ref(v_e_1347_);
v___y_1394_ = v___x_1410_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
lean_inc_ref(v_p_1337_);
lean_inc_ref(v_binderType_1389_);
v___x_1411_ = lean_apply_1(v_p_1337_, v_binderType_1389_);
v___x_1412_ = lean_unbox(v___x_1411_);
if (v___x_1412_ == 0)
{
uint8_t v___x_1413_; 
lean_inc_ref(v_body_1390_);
lean_inc_ref(v_binderType_1389_);
lean_dec_ref(v_e_1347_);
v___x_1413_ = lean_unbox(v___x_1411_);
v___y_1394_ = v___x_1413_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1414_ = lean_unsigned_to_nat(1u);
v___f_1415_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1415_, 0, v___x_1391_);
lean_closure_set(v___f_1415_, 1, v_currentBinderIdx_1339_);
lean_closure_set(v___f_1415_, 2, v___x_1414_);
lean_closure_set(v___f_1415_, 3, v_currentFVars_1340_);
lean_closure_set(v___f_1415_, 4, v_p_1337_);
v___x_1416_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0));
v___x_1417_ = 0;
v___x_1418_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_e_1347_, v___x_1416_, v___f_1415_, v___x_1417_, v___x_1417_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
return v___x_1418_;
}
}
v___jp_1393_:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Meta_mkSorry(v_binderType_1389_, v___y_1394_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = lean_expr_instantiate1(v_body_1390_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_body_1390_);
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_add(v_currentBinderIdx_1339_, v___x_1398_);
lean_dec(v_currentBinderIdx_1339_);
v_e_1338_ = v___x_1397_;
v_currentBinderIdx_1339_ = v___x_1399_;
goto _start;
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v_body_1390_);
lean_dec_ref(v_currentFVars_1340_);
lean_dec(v_currentBinderIdx_1339_);
lean_dec_ref(v_p_1337_);
v_a_1401_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1395_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1395_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v_e_1347_);
lean_dec_ref(v_currentFVars_1340_);
lean_dec(v_currentBinderIdx_1339_);
lean_dec_ref(v_p_1337_);
v_a_1419_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1392_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1392_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(lean_object* v___x_1427_, lean_object* v_currentBinderIdx_1428_, lean_object* v___x_1429_, lean_object* v_currentFVars_1430_, lean_object* v_p_1431_, lean_object* v_fvar_1432_, lean_object* v_e_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = lean_array_get_borrowed(v___x_1427_, v_fvar_1432_, v___x_1440_);
v___x_1442_ = l_Lean_Expr_fvarId_x21(v___x_1441_);
v___x_1443_ = lean_nat_add(v_currentBinderIdx_1428_, v___x_1429_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v_currentBinderIdx_1428_);
v___x_1445_ = lean_array_push(v_currentFVars_1430_, v___x_1444_);
v___x_1446_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1431_, v_e_1433_, v___x_1443_, v___x_1445_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___boxed(lean_object* v_p_1447_, lean_object* v_e_1448_, lean_object* v_currentBinderIdx_1449_, lean_object* v_currentFVars_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1447_, v_e_1448_, v_currentBinderIdx_1449_, v_currentFVars_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(lean_object* v_k_1458_, lean_object* v_t_1459_){
_start:
{
if (lean_obj_tag(v_t_1459_) == 0)
{
lean_object* v_k_1460_; lean_object* v_l_1461_; lean_object* v_r_1462_; uint8_t v___x_1463_; 
v_k_1460_ = lean_ctor_get(v_t_1459_, 1);
v_l_1461_ = lean_ctor_get(v_t_1459_, 3);
v_r_1462_ = lean_ctor_get(v_t_1459_, 4);
v___x_1463_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1458_, v_k_1460_);
switch(v___x_1463_)
{
case 0:
{
v_t_1459_ = v_l_1461_;
goto _start;
}
case 1:
{
uint8_t v___x_1465_; 
v___x_1465_ = 1;
return v___x_1465_;
}
default: 
{
v_t_1459_ = v_r_1462_;
goto _start;
}
}
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = 0;
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg___boxed(lean_object* v_k_1468_, lean_object* v_t_1469_){
_start:
{
uint8_t v_res_1470_; lean_object* v_r_1471_; 
v_res_1470_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_1468_, v_t_1469_);
lean_dec(v_t_1469_);
lean_dec(v_k_1468_);
v_r_1471_ = lean_box(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(lean_object* v_val_1472_, lean_object* v_as_1473_, size_t v_i_1474_, size_t v_stop_1475_, lean_object* v_b_1476_){
_start:
{
lean_object* v___y_1478_; uint8_t v___x_1482_; 
v___x_1482_ = lean_usize_dec_eq(v_i_1474_, v_stop_1475_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v_fvarId_1484_; lean_object* v_idx_1485_; uint8_t v___x_1486_; 
v___x_1483_ = lean_array_uget_borrowed(v_as_1473_, v_i_1474_);
v_fvarId_1484_ = lean_ctor_get(v___x_1483_, 0);
v_idx_1485_ = lean_ctor_get(v___x_1483_, 1);
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_fvarId_1484_, v_val_1472_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
lean_inc(v_idx_1485_);
v___x_1487_ = lean_array_push(v_b_1476_, v_idx_1485_);
v___y_1478_ = v___x_1487_;
goto v___jp_1477_;
}
else
{
v___y_1478_ = v_b_1476_;
goto v___jp_1477_;
}
}
else
{
return v_b_1476_;
}
v___jp_1477_:
{
size_t v___x_1479_; size_t v___x_1480_; 
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1474_, v___x_1479_);
v_i_1474_ = v___x_1480_;
v_b_1476_ = v___y_1478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1___boxed(lean_object* v_val_1488_, lean_object* v_as_1489_, lean_object* v_i_1490_, lean_object* v_stop_1491_, lean_object* v_b_1492_){
_start:
{
size_t v_i_boxed_1493_; size_t v_stop_boxed_1494_; lean_object* v_res_1495_; 
v_i_boxed_1493_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_stop_boxed_1494_ = lean_unbox_usize(v_stop_1491_);
lean_dec(v_stop_1491_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1488_, v_as_1489_, v_i_boxed_1493_, v_stop_boxed_1494_, v_b_1492_);
lean_dec_ref(v_as_1489_);
lean_dec(v_val_1488_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(lean_object* v_val_1496_, lean_object* v_as_1497_, lean_object* v_start_1498_, lean_object* v_stop_1499_){
_start:
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0));
v___x_1501_ = lean_nat_dec_lt(v_start_1498_, v_stop_1499_);
if (v___x_1501_ == 0)
{
return v___x_1500_;
}
else
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = lean_array_get_size(v_as_1497_);
v___x_1503_ = lean_nat_dec_le(v_stop_1499_, v___x_1502_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_nat_dec_lt(v_start_1498_, v___x_1502_);
if (v___x_1504_ == 0)
{
return v___x_1500_;
}
else
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_usize_of_nat(v_start_1498_);
v___x_1506_ = lean_usize_of_nat(v___x_1502_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1496_, v_as_1497_, v___x_1505_, v___x_1506_, v___x_1500_);
return v___x_1507_;
}
}
else
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_usize_of_nat(v_start_1498_);
v___x_1509_ = lean_usize_of_nat(v_stop_1499_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1496_, v_as_1497_, v___x_1508_, v___x_1509_, v___x_1500_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1___boxed(lean_object* v_val_1511_, lean_object* v_as_1512_, lean_object* v_start_1513_, lean_object* v_stop_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v_val_1511_, v_as_1512_, v_start_1513_, v_stop_1514_);
lean_dec(v_stop_1514_);
lean_dec(v_start_1513_);
lean_dec_ref(v_as_1512_);
lean_dec(v_val_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(lean_object* v_p_1518_, lean_object* v_e_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1525_ = lean_box(1);
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0));
v___x_1528_ = lean_st_mk_ref(v___x_1525_);
v___x_1529_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1518_, v_e_1519_, v___x_1526_, v___x_1527_, v___x_1528_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1540_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1534_ = lean_st_ref_get(v___x_1528_);
lean_dec(v___x_1528_);
v___x_1535_ = lean_array_get_size(v_a_1530_);
v___x_1536_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v___x_1534_, v_a_1530_, v___x_1526_, v___x_1535_);
lean_dec(v_a_1530_);
lean_dec(v___x_1534_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1536_);
v___x_1538_ = v___x_1532_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v___x_1528_);
v_a_1541_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1529_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1529_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___boxed(lean_object* v_p_1549_, lean_object* v_e_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_1549_, v_e_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(lean_object* v_00_u03b2_1557_, lean_object* v_k_1558_, lean_object* v_t_1559_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_1558_, v_t_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___boxed(lean_object* v_00_u03b2_1561_, lean_object* v_k_1562_, lean_object* v_t_1563_){
_start:
{
uint8_t v_res_1564_; lean_object* v_r_1565_; 
v_res_1564_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(v_00_u03b2_1561_, v_k_1562_, v_t_1563_);
lean_dec(v_t_1563_);
lean_dec(v_k_1562_);
v_r_1565_ = lean_box(v_res_1564_);
return v_r_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(lean_object* v_k_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v_b_1569_, lean_object* v_c_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
lean_inc(v___y_1574_);
lean_inc_ref(v___y_1573_);
lean_inc(v___y_1572_);
lean_inc_ref(v___y_1571_);
lean_inc(v___y_1568_);
lean_inc_ref(v___y_1567_);
v___x_1576_ = lean_apply_9(v_k_1566_, v_b_1569_, v_c_1570_, v___y_1567_, v___y_1568_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, lean_box(0));
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed(lean_object* v_k_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v_b_1580_, lean_object* v_c_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(v_k_1577_, v___y_1578_, v___y_1579_, v_b_1580_, v_c_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(lean_object* v_type_1588_, lean_object* v_maxFVars_x3f_1589_, lean_object* v_k_1590_, uint8_t v_cleanupAnnotations_1591_, uint8_t v_whnfType_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___f_1600_; lean_object* v___x_1601_; 
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1600_, 0, v_k_1590_);
lean_closure_set(v___f_1600_, 1, v___y_1593_);
lean_closure_set(v___f_1600_, 2, v___y_1594_);
v___x_1601_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1588_, v_maxFVars_x3f_1589_, v___f_1600_, v_cleanupAnnotations_1591_, v_whnfType_1592_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1601_) == 0)
{
return v___x_1601_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___boxed(lean_object* v_type_1610_, lean_object* v_maxFVars_x3f_1611_, lean_object* v_k_1612_, lean_object* v_cleanupAnnotations_1613_, lean_object* v_whnfType_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1622_; uint8_t v_whnfType_boxed_1623_; lean_object* v_res_1624_; 
v_cleanupAnnotations_boxed_1622_ = lean_unbox(v_cleanupAnnotations_1613_);
v_whnfType_boxed_1623_ = lean_unbox(v_whnfType_1614_);
v_res_1624_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1610_, v_maxFVars_x3f_1611_, v_k_1612_, v_cleanupAnnotations_boxed_1622_, v_whnfType_boxed_1623_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(lean_object* v_00_u03b1_1625_, lean_object* v_type_1626_, lean_object* v_maxFVars_x3f_1627_, lean_object* v_k_1628_, uint8_t v_cleanupAnnotations_1629_, uint8_t v_whnfType_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1626_, v_maxFVars_x3f_1627_, v_k_1628_, v_cleanupAnnotations_1629_, v_whnfType_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___boxed(lean_object* v_00_u03b1_1639_, lean_object* v_type_1640_, lean_object* v_maxFVars_x3f_1641_, lean_object* v_k_1642_, lean_object* v_cleanupAnnotations_1643_, lean_object* v_whnfType_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1652_; uint8_t v_whnfType_boxed_1653_; lean_object* v_res_1654_; 
v_cleanupAnnotations_boxed_1652_ = lean_unbox(v_cleanupAnnotations_1643_);
v_whnfType_boxed_1653_ = lean_unbox(v_whnfType_1644_);
v_res_1654_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(v_00_u03b1_1639_, v_type_1640_, v_maxFVars_x3f_1641_, v_k_1642_, v_cleanupAnnotations_boxed_1652_, v_whnfType_boxed_1653_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1654_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(lean_object* v_a_1655_, lean_object* v_as_1656_, size_t v_i_1657_, size_t v_stop_1658_){
_start:
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_usize_dec_eq(v_i_1657_, v_stop_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = lean_array_uget_borrowed(v_as_1656_, v_i_1657_);
v___x_1661_ = lean_nat_dec_eq(v_a_1655_, v___x_1660_);
if (v___x_1661_ == 0)
{
size_t v___x_1662_; size_t v___x_1663_; 
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = lean_usize_add(v_i_1657_, v___x_1662_);
v_i_1657_ = v___x_1663_;
goto _start;
}
else
{
return v___x_1661_;
}
}
else
{
uint8_t v___x_1665_; 
v___x_1665_ = 0;
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0___boxed(lean_object* v_a_1666_, lean_object* v_as_1667_, lean_object* v_i_1668_, lean_object* v_stop_1669_){
_start:
{
size_t v_i_boxed_1670_; size_t v_stop_boxed_1671_; uint8_t v_res_1672_; lean_object* v_r_1673_; 
v_i_boxed_1670_ = lean_unbox_usize(v_i_1668_);
lean_dec(v_i_1668_);
v_stop_boxed_1671_ = lean_unbox_usize(v_stop_1669_);
lean_dec(v_stop_1669_);
v_res_1672_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_1666_, v_as_1667_, v_i_boxed_1670_, v_stop_boxed_1671_);
lean_dec_ref(v_as_1667_);
lean_dec(v_a_1666_);
v_r_1673_ = lean_box(v_res_1672_);
return v_r_1673_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(lean_object* v_as_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = lean_array_get_size(v_as_1674_);
v___x_1678_ = lean_nat_dec_lt(v___x_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
return v___x_1678_;
}
else
{
size_t v___x_1679_; size_t v___x_1680_; uint8_t v___x_1681_; 
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = lean_usize_of_nat(v___x_1677_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_1675_, v_as_1674_, v___x_1679_, v___x_1680_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0___boxed(lean_object* v_as_1682_, lean_object* v_a_1683_){
_start:
{
uint8_t v_res_1684_; lean_object* v_r_1685_; 
v_res_1684_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v_as_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_as_1682_);
v_r_1685_ = lean_box(v_res_1684_);
return v_r_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(lean_object* v___x_1686_, lean_object* v___x_1687_, lean_object* v___x_1688_, uint8_t v___x_1689_, lean_object* v_fvars_1690_, size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_bs_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_bs_1693_);
return v___x_1700_;
}
else
{
uint8_t v___x_1701_; lean_object* v_v_1702_; lean_object* v___x_1703_; lean_object* v_bs_x27_1704_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; lean_object* v___y_1715_; lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1701_ = lean_nat_dec_lt(v___x_1687_, v___x_1688_);
v_v_1702_ = lean_array_uget(v_bs_1693_, v_i_1692_);
v___x_1703_ = lean_unsigned_to_nat(0u);
v_bs_x27_1704_ = lean_array_uset(v_bs_1693_, v_i_1692_, v___x_1703_);
v___x_1718_ = lean_array_get_size(v_fvars_1690_);
v___x_1719_ = lean_nat_dec_lt(v_v_1702_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_box(0);
v___y_1715_ = v___x_1720_;
v_a_1716_ = v___x_1720_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_array_fget_borrowed(v_fvars_1690_, v_v_1702_);
lean_inc_n(v___x_1721_, 2);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
v___x_1723_ = lean_infer_type(v___x_1721_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_a_1724_);
v___y_1715_ = v___x_1722_;
v_a_1716_ = v___x_1725_;
goto v___jp_1714_;
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref_known(v___x_1722_, 1);
lean_dec_ref(v_bs_x27_1704_);
lean_dec(v_v_1702_);
v_a_1726_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1723_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1723_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
v___jp_1705_:
{
lean_object* v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1709_, 0, v___y_1707_);
lean_ctor_set(v___x_1709_, 1, v___y_1706_);
lean_ctor_set(v___x_1709_, 2, v_v_1702_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*3, v___y_1708_);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1692_, v___x_1710_);
v___x_1712_ = lean_array_uset(v_bs_x27_1704_, v_i_1692_, v___x_1709_);
v_i_1692_ = v___x_1711_;
v_bs_1693_ = v___x_1712_;
goto _start;
}
v___jp_1714_:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v___x_1686_, v_v_1702_);
if (v___x_1717_ == 0)
{
v___y_1706_ = v_a_1716_;
v___y_1707_ = v___y_1715_;
v___y_1708_ = v___x_1701_;
goto v___jp_1705_;
}
else
{
v___y_1706_ = v_a_1716_;
v___y_1707_ = v___y_1715_;
v___y_1708_ = v___x_1689_;
goto v___jp_1705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg___boxed(lean_object* v___x_1734_, lean_object* v___x_1735_, lean_object* v___x_1736_, lean_object* v___x_1737_, lean_object* v_fvars_1738_, lean_object* v_sz_1739_, lean_object* v_i_1740_, lean_object* v_bs_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
uint8_t v___x_3282__boxed_1747_; size_t v_sz_boxed_1748_; size_t v_i_boxed_1749_; lean_object* v_res_1750_; 
v___x_3282__boxed_1747_ = lean_unbox(v___x_1737_);
v_sz_boxed_1748_ = lean_unbox_usize(v_sz_1739_);
lean_dec(v_sz_1739_);
v_i_boxed_1749_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1734_, v___x_1735_, v___x_1736_, v___x_3282__boxed_1747_, v_fvars_1738_, v_sz_boxed_1748_, v_i_boxed_1749_, v_bs_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v_fvars_1738_);
lean_dec(v___x_1736_);
lean_dec(v___x_1735_);
lean_dec_ref(v___x_1734_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(lean_object* v_p_1751_, lean_object* v_type_1752_, lean_object* v_a_1753_, lean_object* v___x_1754_, lean_object* v___x_1755_, uint8_t v___x_1756_, lean_object* v_logOnUnused_1757_, lean_object* v_fvars_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; size_t v_sz_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
v___x_1767_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(v_p_1751_, v_type_1752_);
v_sz_1768_ = lean_array_size(v_a_1753_);
v___x_1769_ = ((size_t)0ULL);
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1767_, v___x_1754_, v___x_1755_, v___x_1756_, v_fvars_1758_, v_sz_1768_, v___x_1769_, v_a_1753_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v___x_1767_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
v___x_1772_ = lean_apply_8(v_logOnUnused_1757_, v_a_1771_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, lean_box(0));
return v___x_1772_;
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_logOnUnused_1757_);
v_a_1773_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1770_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1770_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed(lean_object* v_p_1781_, lean_object* v_type_1782_, lean_object* v_a_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v___x_1786_, lean_object* v_logOnUnused_1787_, lean_object* v_fvars_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v___x_3375__boxed_1797_; lean_object* v_res_1798_; 
v___x_3375__boxed_1797_ = lean_unbox(v___x_1786_);
v_res_1798_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(v_p_1781_, v_type_1782_, v_a_1783_, v___x_1784_, v___x_1785_, v___x_3375__boxed_1797_, v_logOnUnused_1787_, v_fvars_1788_, v_x_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_x_1789_);
lean_dec_ref(v_fvars_1788_);
lean_dec(v___x_1785_);
lean_dec(v___x_1784_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(lean_object* v_decl_1799_, lean_object* v_p_1800_, lean_object* v_logOnUnused_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_type_1809_; lean_object* v___x_1810_; 
v_type_1809_ = lean_ctor_get(v_decl_1799_, 2);
lean_inc_ref_n(v_type_1809_, 2);
lean_dec_ref(v_decl_1799_);
lean_inc_ref(v_p_1800_);
v___x_1810_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_1800_, v_type_1809_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1834_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1834_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1834_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = lean_array_get_size(v_a_1811_);
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_nat_sub(v___x_1815_, v___x_1816_);
v___x_1818_ = lean_nat_dec_lt(v___x_1817_, v___x_1815_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_dec(v___x_1817_);
lean_dec(v_a_1811_);
lean_dec_ref(v_type_1809_);
lean_dec_ref(v_logOnUnused_1801_);
lean_dec_ref(v_p_1800_);
v___x_1819_ = lean_box(0);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1819_);
v___x_1821_ = v___x_1813_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
else
{
uint8_t v___x_1823_; 
v___x_1823_ = l_Lean_Expr_hasSorry(v_type_1809_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___f_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_del_object(v___x_1813_);
v___x_1824_ = lean_box(v___x_1823_);
lean_inc(v___x_1817_);
lean_inc(v_a_1811_);
lean_inc_ref(v_type_1809_);
v___f_1825_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1825_, 0, v_p_1800_);
lean_closure_set(v___f_1825_, 1, v_type_1809_);
lean_closure_set(v___f_1825_, 2, v_a_1811_);
lean_closure_set(v___f_1825_, 3, v___x_1817_);
lean_closure_set(v___f_1825_, 4, v___x_1815_);
lean_closure_set(v___f_1825_, 5, v___x_1824_);
lean_closure_set(v___f_1825_, 6, v_logOnUnused_1801_);
v___x_1826_ = lean_array_fget(v_a_1811_, v___x_1817_);
lean_dec(v___x_1817_);
lean_dec(v_a_1811_);
v___x_1827_ = lean_nat_add(v___x_1826_, v___x_1816_);
lean_dec(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
v___x_1829_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1809_, v___x_1828_, v___f_1825_, v___x_1818_, v___x_1823_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
lean_dec(v___x_1817_);
lean_dec(v_a_1811_);
lean_dec_ref(v_type_1809_);
lean_dec_ref(v_logOnUnused_1801_);
lean_dec_ref(v_p_1800_);
v___x_1830_ = lean_box(0);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1830_);
v___x_1832_ = v___x_1813_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec_ref(v_type_1809_);
lean_dec_ref(v_logOnUnused_1801_);
lean_dec_ref(v_p_1800_);
v_a_1835_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1810_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1810_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___boxed(lean_object* v_decl_1843_, lean_object* v_p_1844_, lean_object* v_logOnUnused_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_decl_1843_, v_p_1844_, v_logOnUnused_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(lean_object* v___x_1854_, lean_object* v___x_1855_, lean_object* v___x_1856_, uint8_t v___x_1857_, lean_object* v_fvars_1858_, size_t v_sz_1859_, size_t v_i_1860_, lean_object* v_bs_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1854_, v___x_1855_, v___x_1856_, v___x_1857_, v_fvars_1858_, v_sz_1859_, v_i_1860_, v_bs_1861_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___boxed(lean_object* v___x_1870_, lean_object* v___x_1871_, lean_object* v___x_1872_, lean_object* v___x_1873_, lean_object* v_fvars_1874_, lean_object* v_sz_1875_, lean_object* v_i_1876_, lean_object* v_bs_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
uint8_t v___x_3506__boxed_1885_; size_t v_sz_boxed_1886_; size_t v_i_boxed_1887_; lean_object* v_res_1888_; 
v___x_3506__boxed_1885_ = lean_unbox(v___x_1873_);
v_sz_boxed_1886_ = lean_unbox_usize(v_sz_1875_);
lean_dec(v_sz_1875_);
v_i_boxed_1887_ = lean_unbox_usize(v_i_1876_);
lean_dec(v_i_1876_);
v_res_1888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(v___x_1870_, v___x_1871_, v___x_1872_, v___x_3506__boxed_1885_, v_fvars_1874_, v_sz_boxed_1886_, v_i_boxed_1887_, v_bs_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_fvars_1874_);
lean_dec(v___x_1872_);
lean_dec(v___x_1871_);
lean_dec_ref(v___x_1870_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(lean_object* v_env_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
if (lean_obj_tag(v_a_1890_) == 0)
{
lean_object* v___x_1892_; 
lean_dec_ref(v_env_1889_);
v___x_1892_ = lean_array_to_list(v_a_1891_);
return v___x_1892_;
}
else
{
lean_object* v_head_1893_; lean_object* v_tail_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; 
v_head_1893_ = lean_ctor_get(v_a_1890_, 0);
lean_inc(v_head_1893_);
v_tail_1894_ = lean_ctor_get(v_a_1890_, 1);
lean_inc(v_tail_1894_);
lean_dec_ref_known(v_a_1890_, 2);
v___x_1895_ = 0;
lean_inc_ref(v_env_1889_);
v___x_1896_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_1889_, v_head_1893_, v___x_1895_);
if (lean_obj_tag(v___x_1896_) == 0)
{
v_a_1890_ = v_tail_1894_;
goto _start;
}
else
{
lean_object* v_val_1898_; lean_object* v___x_1899_; 
v_val_1898_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_val_1898_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1899_ = lean_array_push(v_a_1891_, v_val_1898_);
v_a_1890_ = v_tail_1894_;
v_a_1891_ = v___x_1899_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(lean_object* v_t_1903_, lean_object* v_env_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_Linter_getDeclsByBody(v_t_1903_);
v___x_1906_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0));
v___x_1907_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(v_env_1904_, v___x_1905_, v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(lean_object* v_n_1926_){
_start:
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1));
v___x_1928_ = lean_name_eq(v_n_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3));
v___x_1930_ = lean_name_eq(v_n_1926_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5));
v___x_1932_ = lean_name_eq(v_n_1926_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7));
v___x_1934_ = lean_name_eq(v_n_1926_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9));
v___x_1936_ = lean_name_eq(v_n_1926_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1937_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11));
v___x_1938_ = lean_name_eq(v_n_1926_, v___x_1937_);
return v___x_1938_;
}
else
{
return v___x_1936_;
}
}
else
{
return v___x_1934_;
}
}
else
{
return v___x_1932_;
}
}
else
{
return v___x_1930_;
}
}
else
{
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___boxed(lean_object* v_n_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(v_n_1939_);
lean_dec(v_n_1939_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(lean_object* v_type_1943_){
_start:
{
lean_object* v___f_1944_; uint8_t v___x_1945_; 
v___f_1944_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0));
v___x_1945_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(v___f_1944_, v_type_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___boxed(lean_object* v_type_1946_){
_start:
{
uint8_t v_res_1947_; lean_object* v_r_1948_; 
v_res_1947_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(v_type_1946_);
v_r_1948_ = lean_box(v_res_1947_);
return v_r_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; lean_object* v_infoState_1952_; lean_object* v_trees_1953_; lean_object* v___x_1954_; 
v___x_1951_ = lean_st_ref_get(v___y_1949_);
v_infoState_1952_ = lean_ctor_get(v___x_1951_, 8);
lean_inc_ref(v_infoState_1952_);
lean_dec(v___x_1951_);
v_trees_1953_ = lean_ctor_get(v_infoState_1952_, 2);
lean_inc_ref(v_trees_1953_);
lean_dec_ref(v_infoState_1952_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_trees_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg___boxed(lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_1955_);
lean_dec(v___y_1955_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___boxed(lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(uint8_t v___x_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
if (lean_obj_tag(v_a_1968_) == 0)
{
lean_object* v___x_1970_; 
v___x_1970_ = l_List_reverse___redArg(v_a_1969_);
return v___x_1970_;
}
else
{
lean_object* v_head_1971_; lean_object* v_tail_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1990_; 
v_head_1971_ = lean_ctor_get(v_a_1968_, 0);
v_tail_1972_ = lean_ctor_get(v_a_1968_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1974_ = v_a_1968_;
v_isShared_1975_ = v_isSharedCheck_1990_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_tail_1972_);
lean_inc(v_head_1971_);
lean_dec(v_a_1968_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1990_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
uint8_t v___y_1977_; lean_object* v_name_1983_; lean_object* v_type_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_name_1983_ = lean_ctor_get(v_head_1971_, 0);
v_type_1984_ = lean_ctor_get(v_head_1971_, 2);
v___x_1985_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1));
lean_inc(v_name_1983_);
v___x_1986_ = l_Lean_privateToUserName(v_name_1983_);
v___x_1987_ = l_Lean_Name_isPrefixOf(v___x_1985_, v___x_1986_);
lean_dec(v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0));
lean_inc_ref(v_type_1984_);
v___x_1989_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(v___x_1988_, v_type_1984_);
v___y_1977_ = v___x_1989_;
goto v___jp_1976_;
}
else
{
v___y_1977_ = v___x_1967_;
goto v___jp_1976_;
}
v___jp_1976_:
{
if (v___y_1977_ == 0)
{
lean_del_object(v___x_1974_);
lean_dec(v_head_1971_);
v_a_1968_ = v_tail_1972_;
goto _start;
}
else
{
lean_object* v___x_1980_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v_a_1969_);
v___x_1980_ = v___x_1974_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_head_1971_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_a_1969_);
v___x_1980_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v_a_1968_ = v_tail_1972_;
v_a_1969_ = v___x_1980_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___boxed(lean_object* v___x_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
uint8_t v___x_11732__boxed_1994_; lean_object* v_res_1995_; 
v___x_11732__boxed_1994_ = lean_unbox(v___x_1991_);
v_res_1995_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_11732__boxed_1994_, v_a_1992_, v_a_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(lean_object* v_o_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v_env_2001_; lean_object* v___x_2002_; lean_object* v_toEnvExtension_2003_; lean_object* v_asyncMode_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v_merged_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v___x_1999_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2000_ = lean_st_ref_get(v___y_1997_);
v_env_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc_ref(v_env_2001_);
lean_dec(v___x_2000_);
v___x_2002_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2003_ = lean_ctor_get(v___x_2002_, 0);
v_asyncMode_2004_ = lean_ctor_get(v_toEnvExtension_2003_, 2);
v___x_2005_ = lean_box(0);
v___x_2006_ = 0;
v___x_2007_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1999_, v___x_2002_, v_env_2001_, v_asyncMode_2004_, v___x_2005_, v___x_2006_);
v_merged_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v___x_2007_, 1);
lean_dec(v_unused_2017_);
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_merged_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_merged_2008_);
lean_ctor_set(v___x_2010_, 0, v_o_1996_);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_o_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_merged_2008_);
v___x_2013_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
return v___x_2014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_o_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_o_2018_, v___y_2019_);
lean_dec(v___y_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2026_);
v___x_2030_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v___x_2029_, v___y_2027_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3___boxed(lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(lean_object* v_msgData_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; lean_object* v_env_2046_; uint8_t v___x_2047_; lean_object* v_env_2048_; lean_object* v___x_2049_; lean_object* v_toCold_2050_; lean_object* v_mctx_2051_; lean_object* v_lctx_2052_; lean_object* v_options_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2045_ = lean_st_ref_get(v___y_2043_);
v_env_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_env_2046_);
lean_dec(v___x_2045_);
v___x_2047_ = 0;
v_env_2048_ = l_Lean_Environment_setRecordingDeps(v_env_2046_, v___x_2047_);
v___x_2049_ = lean_st_ref_get(v___y_2041_);
v_toCold_2050_ = lean_ctor_get(v___y_2042_, 0);
v_mctx_2051_ = lean_ctor_get(v___x_2049_, 0);
lean_inc_ref(v_mctx_2051_);
lean_dec(v___x_2049_);
v_lctx_2052_ = lean_ctor_get(v___y_2040_, 2);
v_options_2053_ = lean_ctor_get(v_toCold_2050_, 2);
lean_inc_ref(v_options_2053_);
lean_inc_ref(v_lctx_2052_);
v___x_2054_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2054_, 0, v_env_2048_);
lean_ctor_set(v___x_2054_, 1, v_mctx_2051_);
lean_ctor_set(v___x_2054_, 2, v_lctx_2052_);
lean_ctor_set(v___x_2054_, 3, v_options_2053_);
v___x_2055_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v_msgData_2039_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13___boxed(lean_object* v_msgData_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(v_msgData_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(lean_object* v_opts_2064_, lean_object* v_opt_2065_){
_start:
{
lean_object* v_name_2066_; lean_object* v_defValue_2067_; lean_object* v_map_2068_; lean_object* v___x_2069_; 
v_name_2066_ = lean_ctor_get(v_opt_2065_, 0);
v_defValue_2067_ = lean_ctor_get(v_opt_2065_, 1);
v_map_2068_ = lean_ctor_get(v_opts_2064_, 0);
v___x_2069_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2068_, v_name_2066_);
if (lean_obj_tag(v___x_2069_) == 0)
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_unbox(v_defValue_2067_);
return v___x_2070_;
}
else
{
lean_object* v_val_2071_; 
v_val_2071_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v___x_2069_, 1);
if (lean_obj_tag(v_val_2071_) == 1)
{
uint8_t v_v_2072_; 
v_v_2072_ = lean_ctor_get_uint8(v_val_2071_, 0);
lean_dec_ref_known(v_val_2071_, 0);
return v_v_2072_;
}
else
{
uint8_t v___x_2073_; 
lean_dec(v_val_2071_);
v___x_2073_ = lean_unbox(v_defValue_2067_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14___boxed(lean_object* v_opts_2074_, lean_object* v_opt_2075_){
_start:
{
uint8_t v_res_2076_; lean_object* v_r_2077_; 
v_res_2076_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(v_opts_2074_, v_opt_2075_);
lean_dec_ref(v_opt_2075_);
lean_dec_ref(v_opts_2074_);
v_r_2077_ = lean_box(v_res_2076_);
return v_r_2077_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(uint8_t v_suppressElabErrors_2086_, lean_object* v_x_2087_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 1)
{
lean_object* v_pre_2088_; 
v_pre_2088_ = lean_ctor_get(v_x_2087_, 0);
switch(lean_obj_tag(v_pre_2088_))
{
case 1:
{
lean_object* v_pre_2089_; 
v_pre_2089_ = lean_ctor_get(v_pre_2088_, 0);
switch(lean_obj_tag(v_pre_2089_))
{
case 0:
{
lean_object* v_str_2090_; lean_object* v_str_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_str_2090_ = lean_ctor_get(v_x_2087_, 1);
v_str_2091_ = lean_ctor_get(v_pre_2088_, 1);
v___x_2092_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__0));
v___x_2093_ = lean_string_dec_eq(v_str_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__1));
v___x_2095_ = lean_string_dec_eq(v_str_2091_, v___x_2094_);
if (v___x_2095_ == 0)
{
return v___x_2095_;
}
else
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__2));
v___x_2097_ = lean_string_dec_eq(v_str_2090_, v___x_2096_);
if (v___x_2097_ == 0)
{
return v___x_2097_;
}
else
{
return v_suppressElabErrors_2086_;
}
}
}
else
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__3));
v___x_2099_ = lean_string_dec_eq(v_str_2090_, v___x_2098_);
if (v___x_2099_ == 0)
{
return v___x_2099_;
}
else
{
return v_suppressElabErrors_2086_;
}
}
}
case 1:
{
lean_object* v_pre_2100_; 
v_pre_2100_ = lean_ctor_get(v_pre_2089_, 0);
if (lean_obj_tag(v_pre_2100_) == 0)
{
lean_object* v_str_2101_; lean_object* v_str_2102_; lean_object* v_str_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v_str_2101_ = lean_ctor_get(v_x_2087_, 1);
v_str_2102_ = lean_ctor_get(v_pre_2088_, 1);
v_str_2103_ = lean_ctor_get(v_pre_2089_, 1);
v___x_2104_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__4));
v___x_2105_ = lean_string_dec_eq(v_str_2103_, v___x_2104_);
if (v___x_2105_ == 0)
{
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__5));
v___x_2107_ = lean_string_dec_eq(v_str_2102_, v___x_2106_);
if (v___x_2107_ == 0)
{
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__6));
v___x_2109_ = lean_string_dec_eq(v_str_2101_, v___x_2108_);
if (v___x_2109_ == 0)
{
return v___x_2109_;
}
else
{
return v_suppressElabErrors_2086_;
}
}
}
}
else
{
uint8_t v___x_2110_; 
v___x_2110_ = 0;
return v___x_2110_;
}
}
default: 
{
uint8_t v___x_2111_; 
v___x_2111_ = 0;
return v___x_2111_;
}
}
}
case 0:
{
lean_object* v_str_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_str_2112_ = lean_ctor_get(v_x_2087_, 1);
v___x_2113_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__7));
v___x_2114_ = lean_string_dec_eq(v_str_2112_, v___x_2113_);
if (v___x_2114_ == 0)
{
return v___x_2114_;
}
else
{
return v_suppressElabErrors_2086_;
}
}
default: 
{
uint8_t v___x_2115_; 
v___x_2115_ = 0;
return v___x_2115_;
}
}
}
else
{
uint8_t v___x_2116_; 
v___x_2116_ = 0;
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2117_, lean_object* v_x_2118_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2119_; uint8_t v_res_2120_; lean_object* v_r_2121_; 
v_suppressElabErrors_boxed_2119_ = lean_unbox(v_suppressElabErrors_2117_);
v_res_2120_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(v_suppressElabErrors_boxed_2119_, v_x_2118_);
lean_dec(v_x_2118_);
v_r_2121_ = lean_box(v_res_2120_);
return v_r_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_ref_2122_, lean_object* v_msgData_2123_, uint8_t v_severity_2124_, uint8_t v_isSilent_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___y_2132_; lean_object* v___y_2133_; uint8_t v___y_2134_; lean_object* v___y_2135_; uint8_t v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v_toCold_2139_; lean_object* v___y_2140_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; uint8_t v___y_2172_; lean_object* v___y_2173_; uint8_t v___y_2174_; uint8_t v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2196_; uint8_t v___y_2197_; lean_object* v___y_2198_; uint8_t v___y_2199_; uint8_t v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; uint8_t v___y_2206_; uint8_t v___y_2207_; uint8_t v___x_2217_; uint8_t v___y_2219_; uint8_t v___x_2225_; 
v___x_2217_ = 2;
v___x_2225_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2124_, v___x_2217_);
if (v___x_2225_ == 0)
{
v___y_2219_ = v___x_2225_;
goto v___jp_2218_;
}
else
{
uint8_t v___x_2226_; 
lean_inc_ref(v_msgData_2123_);
v___x_2226_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2123_);
if (v___x_2226_ == 0)
{
v___y_2219_ = v___x_2226_;
goto v___jp_2218_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec_ref(v_msgData_2123_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
}
v___jp_2131_:
{
lean_object* v_currNamespace_2141_; lean_object* v_openDecls_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_env_2147_; lean_object* v_nextMacroScope_2148_; lean_object* v_ngen_2149_; lean_object* v_auxDeclNGen_2150_; lean_object* v_traceState_2151_; lean_object* v_cache_2152_; lean_object* v_recordedDeps_2153_; lean_object* v_messages_2154_; lean_object* v_infoState_2155_; lean_object* v_snapshotTasks_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2167_; 
v_currNamespace_2141_ = lean_ctor_get(v_toCold_2139_, 4);
v_openDecls_2142_ = lean_ctor_get(v_toCold_2139_, 5);
lean_inc(v_openDecls_2142_);
lean_inc(v_currNamespace_2141_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v_currNamespace_2141_);
lean_ctor_set(v___x_2143_, 1, v_openDecls_2142_);
v___x_2144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set(v___x_2144_, 1, v___y_2132_);
lean_inc_ref(v___y_2137_);
lean_inc_ref(v___y_2138_);
v___x_2145_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2145_, 0, v___y_2138_);
lean_ctor_set(v___x_2145_, 1, v___y_2135_);
lean_ctor_set(v___x_2145_, 2, v___y_2133_);
lean_ctor_set(v___x_2145_, 3, v___y_2137_);
lean_ctor_set(v___x_2145_, 4, v___x_2144_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*5, v___y_2134_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*5 + 1, v___y_2136_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*5 + 2, v_isSilent_2125_);
v___x_2146_ = lean_st_ref_take(v___y_2140_);
v_env_2147_ = lean_ctor_get(v___x_2146_, 0);
v_nextMacroScope_2148_ = lean_ctor_get(v___x_2146_, 1);
v_ngen_2149_ = lean_ctor_get(v___x_2146_, 2);
v_auxDeclNGen_2150_ = lean_ctor_get(v___x_2146_, 3);
v_traceState_2151_ = lean_ctor_get(v___x_2146_, 4);
v_cache_2152_ = lean_ctor_get(v___x_2146_, 5);
v_recordedDeps_2153_ = lean_ctor_get(v___x_2146_, 6);
v_messages_2154_ = lean_ctor_get(v___x_2146_, 7);
v_infoState_2155_ = lean_ctor_get(v___x_2146_, 8);
v_snapshotTasks_2156_ = lean_ctor_get(v___x_2146_, 9);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2158_ = v___x_2146_;
v_isShared_2159_ = v_isSharedCheck_2167_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_snapshotTasks_2156_);
lean_inc(v_infoState_2155_);
lean_inc(v_messages_2154_);
lean_inc(v_recordedDeps_2153_);
lean_inc(v_cache_2152_);
lean_inc(v_traceState_2151_);
lean_inc(v_auxDeclNGen_2150_);
lean_inc(v_ngen_2149_);
lean_inc(v_nextMacroScope_2148_);
lean_inc(v_env_2147_);
lean_dec(v___x_2146_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2167_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2160_ = lean_box(0);
v___x_2161_ = l_Lean_MessageLog_add(v___x_2145_, v_messages_2154_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 7, v___x_2161_);
v___x_2163_ = v___x_2158_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_env_2147_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_nextMacroScope_2148_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_ngen_2149_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_auxDeclNGen_2150_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v_traceState_2151_);
lean_ctor_set(v_reuseFailAlloc_2166_, 5, v_cache_2152_);
lean_ctor_set(v_reuseFailAlloc_2166_, 6, v_recordedDeps_2153_);
lean_ctor_set(v_reuseFailAlloc_2166_, 7, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2166_, 8, v_infoState_2155_);
lean_ctor_set(v_reuseFailAlloc_2166_, 9, v_snapshotTasks_2156_);
v___x_2163_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_st_ref_put(v___y_2140_, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2160_);
return v___x_2165_;
}
}
}
v___jp_2168_:
{
lean_object* v_fileName_2177_; lean_object* v_fileMap_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2194_; 
v_fileName_2177_ = lean_ctor_get(v___y_2173_, 0);
v_fileMap_2178_ = lean_ctor_get(v___y_2173_, 1);
v___x_2179_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2123_);
v___x_2180_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(v___x_2179_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2194_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2194_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_inc_ref_n(v_fileMap_2178_, 2);
v___x_2185_ = l_Lean_FileMap_toPosition(v_fileMap_2178_, v___y_2171_);
lean_dec(v___y_2171_);
v___x_2186_ = l_Lean_FileMap_toPosition(v_fileMap_2178_, v___y_2176_);
lean_dec(v___y_2176_);
v___x_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
v___x_2188_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4));
if (v___y_2175_ == 0)
{
lean_del_object(v___x_2183_);
lean_dec_ref(v___y_2170_);
v___y_2132_ = v_a_2181_;
v___y_2133_ = v___x_2187_;
v___y_2134_ = v___y_2172_;
v___y_2135_ = v___x_2185_;
v___y_2136_ = v___y_2174_;
v___y_2137_ = v___x_2188_;
v___y_2138_ = v_fileName_2177_;
v_toCold_2139_ = v___y_2169_;
v___y_2140_ = v___y_2129_;
goto v___jp_2131_;
}
else
{
uint8_t v___x_2189_; 
lean_inc(v_a_2181_);
v___x_2189_ = l_Lean_MessageData_hasTag(v___y_2170_, v_a_2181_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec_ref_known(v___x_2187_, 1);
lean_dec_ref(v___x_2185_);
lean_dec(v_a_2181_);
v___x_2190_ = lean_box(0);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2190_);
v___x_2192_ = v___x_2183_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_del_object(v___x_2183_);
v___y_2132_ = v_a_2181_;
v___y_2133_ = v___x_2187_;
v___y_2134_ = v___y_2172_;
v___y_2135_ = v___x_2185_;
v___y_2136_ = v___y_2174_;
v___y_2137_ = v___x_2188_;
v___y_2138_ = v_fileName_2177_;
v_toCold_2139_ = v___y_2169_;
v___y_2140_ = v___y_2129_;
goto v___jp_2131_;
}
}
}
}
v___jp_2195_:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Syntax_getTailPos_x3f(v___y_2201_, v___y_2199_);
lean_dec(v___y_2201_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_inc(v___y_2202_);
v___y_2169_ = v___y_2196_;
v___y_2170_ = v___y_2198_;
v___y_2171_ = v___y_2202_;
v___y_2172_ = v___y_2199_;
v___y_2173_ = v___y_2196_;
v___y_2174_ = v___y_2200_;
v___y_2175_ = v___y_2197_;
v___y_2176_ = v___y_2202_;
goto v___jp_2168_;
}
else
{
lean_object* v_val_2204_; 
v_val_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___y_2169_ = v___y_2196_;
v___y_2170_ = v___y_2198_;
v___y_2171_ = v___y_2202_;
v___y_2172_ = v___y_2199_;
v___y_2173_ = v___y_2196_;
v___y_2174_ = v___y_2200_;
v___y_2175_ = v___y_2197_;
v___y_2176_ = v_val_2204_;
goto v___jp_2168_;
}
}
v___jp_2205_:
{
lean_object* v_toCold_2208_; lean_object* v_ref_2209_; uint8_t v_suppressElabErrors_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v_ref_2213_; lean_object* v___x_2214_; 
v_toCold_2208_ = lean_ctor_get(v___y_2128_, 0);
v_ref_2209_ = lean_ctor_get(v___y_2128_, 2);
v_suppressElabErrors_2210_ = lean_ctor_get_uint8(v___y_2128_, sizeof(void*)*3 + 2);
v___x_2211_ = lean_box(v_suppressElabErrors_2210_);
v___f_2212_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2212_, 0, v___x_2211_);
v_ref_2213_ = l_Lean_replaceRef(v_ref_2122_, v_ref_2209_);
v___x_2214_ = l_Lean_Syntax_getPos_x3f(v_ref_2213_, v___y_2206_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_unsigned_to_nat(0u);
v___y_2196_ = v_toCold_2208_;
v___y_2197_ = v_suppressElabErrors_2210_;
v___y_2198_ = v___f_2212_;
v___y_2199_ = v___y_2206_;
v___y_2200_ = v___y_2207_;
v___y_2201_ = v_ref_2213_;
v___y_2202_ = v___x_2215_;
goto v___jp_2195_;
}
else
{
lean_object* v_val_2216_; 
v_val_2216_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2216_);
lean_dec_ref_known(v___x_2214_, 1);
v___y_2196_ = v_toCold_2208_;
v___y_2197_ = v_suppressElabErrors_2210_;
v___y_2198_ = v___f_2212_;
v___y_2199_ = v___y_2206_;
v___y_2200_ = v___y_2207_;
v___y_2201_ = v_ref_2213_;
v___y_2202_ = v_val_2216_;
goto v___jp_2195_;
}
}
v___jp_2218_:
{
uint8_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = 1;
v___x_2221_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2124_, v___x_2220_);
if (v___x_2221_ == 0)
{
v___y_2206_ = v___y_2219_;
v___y_2207_ = v_severity_2124_;
goto v___jp_2205_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2222_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2128_);
v___x_2223_ = l_Lean_warningAsError;
v___x_2224_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(v___x_2222_, v___x_2223_);
lean_dec_ref(v___x_2222_);
if (v___x_2224_ == 0)
{
v___y_2206_ = v___y_2219_;
v___y_2207_ = v_severity_2124_;
goto v___jp_2205_;
}
else
{
v___y_2206_ = v___y_2219_;
v___y_2207_ = v___x_2217_;
goto v___jp_2205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_ref_2229_, lean_object* v_msgData_2230_, lean_object* v_severity_2231_, lean_object* v_isSilent_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v_severity_boxed_2238_; uint8_t v_isSilent_boxed_2239_; lean_object* v_res_2240_; 
v_severity_boxed_2238_ = lean_unbox(v_severity_2231_);
v_isSilent_boxed_2239_ = lean_unbox(v_isSilent_2232_);
v_res_2240_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2229_, v_msgData_2230_, v_severity_boxed_2238_, v_isSilent_boxed_2239_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v_ref_2229_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(lean_object* v_ref_2241_, lean_object* v_msgData_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = 1;
v___x_2251_ = 0;
v___x_2252_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2241_, v_msgData_2242_, v___x_2250_, v___x_2251_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6___boxed(lean_object* v_ref_2253_, lean_object* v_msgData_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(v_ref_2253_, v_msgData_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v_ref_2253_);
return v_res_2262_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__0));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__2));
v___x_2268_ = l_Lean_stringToMessageData(v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(lean_object* v_linterOption_2269_, lean_object* v_stx_2270_, lean_object* v_msg_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_name_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2297_; 
v_name_2279_ = lean_ctor_get(v_linterOption_2269_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_linterOption_2269_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; 
v_unused_2298_ = lean_ctor_get(v_linterOption_2269_, 1);
lean_dec(v_unused_2298_);
v___x_2281_ = v_linterOption_2269_;
v_isShared_2282_ = v_isSharedCheck_2297_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_name_2279_);
lean_dec(v_linterOption_2269_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2297_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2283_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1);
lean_inc(v_name_2279_);
v___x_2284_ = l_Lean_MessageData_ofName(v_name_2279_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set_tag(v___x_2281_, 7);
lean_ctor_set(v___x_2281_, 1, v___x_2284_);
lean_ctor_set(v___x_2281_, 0, v___x_2283_);
v___x_2286_ = v___x_2281_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v_disable_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2287_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v_disable_2289_ = l_Lean_MessageData_note(v___x_2288_);
v___x_2290_ = l_Lean_Linter_linterMessageTag;
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_msg_2271_);
lean_ctor_set(v___x_2291_, 1, v_disable_2289_);
v___x_2292_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2293_, 0, v_name_2279_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
lean_inc(v_stx_2270_);
v___x_2294_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2294_, 0, v_stx_2270_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(v_stx_2270_, v___x_2294_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v_stx_2270_);
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___boxed(lean_object* v_linterOption_2299_, lean_object* v_stx_2300_, lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(v_linterOption_2299_, v_stx_2300_, v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(lean_object* v_linterOption_2310_, lean_object* v_stx_2311_, lean_object* v_msg_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2331_; 
v___x_2320_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2331_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2331_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
uint8_t v___x_2325_; 
v___x_2325_ = l_Lean_Linter_getLinterValue(v_linterOption_2310_, v_a_2321_);
lean_dec(v_a_2321_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
lean_dec_ref(v_msg_2312_);
lean_dec(v_stx_2311_);
lean_dec_ref(v_linterOption_2310_);
v___x_2326_ = lean_box(0);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2326_);
v___x_2328_ = v___x_2323_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
else
{
lean_object* v___x_2330_; 
lean_del_object(v___x_2323_);
v___x_2330_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(v_linterOption_2310_, v_stx_2311_, v_msg_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___boxed(lean_object* v_linterOption_2332_, lean_object* v_stx_2333_, lean_object* v_msg_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v_linterOption_2332_, v_stx_2333_, v_msg_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2342_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0));
v___x_2345_ = l_Lean_stringToMessageData(v___x_2344_);
return v___x_2345_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(lean_object* v_head_2351_, lean_object* v___x_2352_, lean_object* v_unusedParams_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_ref_2361_; lean_object* v_name_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___y_2367_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_ref_2361_ = lean_ctor_get(v___y_2358_, 2);
v_name_2362_ = lean_ctor_get(v_head_2351_, 0);
lean_inc(v_name_2362_);
lean_dec_ref(v_head_2351_);
lean_inc_ref(v_unusedParams_2353_);
v___x_2363_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(v_name_2362_, v_unusedParams_2353_);
v___x_2364_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2373_ = lean_array_get_size(v_unusedParams_2353_);
lean_dec_ref(v_unusedParams_2353_);
v___x_2374_ = lean_unsigned_to_nat(1u);
v___x_2375_ = lean_nat_dec_eq(v___x_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
v___x_2376_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4));
v___y_2367_ = v___x_2376_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2377_; 
v___x_2377_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5));
v___y_2367_ = v___x_2377_;
goto v___jp_2366_;
}
v___jp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_inc_ref(v___y_2367_);
v___x_2368_ = l_Lean_stringToMessageData(v___y_2367_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2365_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
lean_inc(v_ref_2361_);
v___x_2372_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_2352_, v_ref_2361_, v___x_2371_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
return v___x_2372_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed(lean_object* v_head_2378_, lean_object* v___x_2379_, lean_object* v_unusedParams_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(v_head_2378_, v___x_2379_, v_unusedParams_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(lean_object* v_as_x27_2389_, lean_object* v_b_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
if (lean_obj_tag(v_as_x27_2389_) == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2398_, 0, v_b_2390_);
return v___x_2398_;
}
else
{
lean_object* v_head_2399_; lean_object* v_tail_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_head_2399_ = lean_ctor_get(v_as_x27_2389_, 0);
v_tail_2400_ = lean_ctor_get(v_as_x27_2389_, 1);
v___x_2401_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
v___x_2402_ = lean_box(0);
lean_inc_n(v_head_2399_, 2);
v___f_2403_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2403_, 0, v_head_2399_);
lean_closure_set(v___f_2403_, 1, v___x_2401_);
v___x_2404_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0));
v___x_2405_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_head_2399_, v___x_2404_, v___f_2403_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_dec_ref_known(v___x_2405_, 1);
v_as_x27_2389_ = v_tail_2400_;
v_b_2390_ = v___x_2402_;
goto _start;
}
else
{
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___boxed(lean_object* v_as_x27_2407_, lean_object* v_b_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_2407_, v_b_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_as_x27_2407_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(lean_object* v___x_2417_, lean_object* v___x_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v___x_2417_, v___x_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v___x_2426_, 0);
lean_dec(v_unused_2434_);
v___x_2428_ = v___x_2426_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_dec(v___x_2426_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2418_);
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2418_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed(lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(v___x_2435_, v___x_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___x_2435_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(lean_object* v___x_2445_, uint8_t v___x_2446_, lean_object* v_as_2447_, size_t v_sz_2448_, size_t v_i_2449_, lean_object* v_b_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_usize_dec_lt(v_i_2449_, v_sz_2448_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref(v___x_2445_);
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_b_2450_);
return v___x_2455_;
}
else
{
lean_object* v___x_2456_; lean_object* v_a_2458_; lean_object* v___x_2463_; lean_object* v_a_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; 
lean_dec_ref(v_b_2450_);
v___x_2456_ = lean_box(0);
v___x_2463_ = lean_box(0);
v_a_2464_ = lean_array_uget_borrowed(v_as_2447_, v_i_2449_);
lean_inc_ref(v___x_2445_);
lean_inc(v_a_2464_);
v___x_2465_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2464_, v___x_2445_);
v___x_2466_ = lean_box(0);
v___x_2467_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2446_, v___x_2465_, v___x_2466_);
v___x_2468_ = l_List_isEmpty___redArg(v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___f_2469_; lean_object* v___x_2470_; 
v___f_2469_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2469_, 0, v___x_2467_);
lean_closure_set(v___f_2469_, 1, v___x_2463_);
v___x_2470_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2469_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_dec_ref_known(v___x_2470_, 1);
v_a_2458_ = v___x_2463_;
goto v___jp_2457_;
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref(v___x_2445_);
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_dec(v___x_2467_);
v_a_2458_ = v___x_2463_;
goto v___jp_2457_;
}
v___jp_2457_:
{
lean_object* v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; 
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2456_);
lean_ctor_set(v___x_2459_, 1, v_a_2458_);
v___x_2460_ = ((size_t)1ULL);
v___x_2461_ = lean_usize_add(v_i_2449_, v___x_2460_);
v_i_2449_ = v___x_2461_;
v_b_2450_ = v___x_2459_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14___boxed(lean_object* v___x_2479_, lean_object* v___x_2480_, lean_object* v_as_2481_, lean_object* v_sz_2482_, lean_object* v_i_2483_, lean_object* v_b_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
uint8_t v___x_12462__boxed_2488_; size_t v_sz_boxed_2489_; size_t v_i_boxed_2490_; lean_object* v_res_2491_; 
v___x_12462__boxed_2488_ = lean_unbox(v___x_2480_);
v_sz_boxed_2489_ = lean_unbox_usize(v_sz_2482_);
lean_dec(v_sz_2482_);
v_i_boxed_2490_ = lean_unbox_usize(v_i_2483_);
lean_dec(v_i_2483_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_2479_, v___x_12462__boxed_2488_, v_as_2481_, v_sz_boxed_2489_, v_i_boxed_2490_, v_b_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec_ref(v_as_2481_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(lean_object* v___x_2495_, uint8_t v___x_2496_, lean_object* v_as_2497_, size_t v_sz_2498_, size_t v_i_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_usize_dec_lt(v_i_2499_, v_sz_2498_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
lean_dec_ref(v___x_2495_);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_b_2500_);
return v___x_2505_;
}
else
{
lean_object* v___x_2506_; lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
lean_dec_ref(v_b_2500_);
v___x_2506_ = lean_box(0);
v_a_2512_ = lean_array_uget_borrowed(v_as_2497_, v_i_2499_);
lean_inc_ref(v___x_2495_);
lean_inc(v_a_2512_);
v___x_2513_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2512_, v___x_2495_);
v___x_2514_ = lean_box(0);
v___x_2515_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2496_, v___x_2513_, v___x_2514_);
v___x_2516_ = l_List_isEmpty___redArg(v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___f_2517_; lean_object* v___x_2518_; 
v___f_2517_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2517_, 0, v___x_2515_);
lean_closure_set(v___f_2517_, 1, v___x_2506_);
v___x_2518_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2517_, v___y_2501_, v___y_2502_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_dec_ref_known(v___x_2518_, 1);
goto v___jp_2507_;
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec_ref(v___x_2495_);
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
else
{
lean_dec(v___x_2515_);
goto v___jp_2507_;
}
v___jp_2507_:
{
lean_object* v___x_2508_; size_t v___x_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0));
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_add(v_i_2499_, v___x_2509_);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_2495_, v___x_2496_, v_as_2497_, v_sz_2498_, v___x_2510_, v___x_2508_, v___y_2501_, v___y_2502_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___boxed(lean_object* v___x_2527_, lean_object* v___x_2528_, lean_object* v_as_2529_, lean_object* v_sz_2530_, lean_object* v_i_2531_, lean_object* v_b_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
uint8_t v___x_12532__boxed_2536_; size_t v_sz_boxed_2537_; size_t v_i_boxed_2538_; lean_object* v_res_2539_; 
v___x_12532__boxed_2536_ = lean_unbox(v___x_2528_);
v_sz_boxed_2537_ = lean_unbox_usize(v_sz_2530_);
lean_dec(v_sz_2530_);
v_i_boxed_2538_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_res_2539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_2527_, v___x_12532__boxed_2536_, v_as_2529_, v_sz_boxed_2537_, v_i_boxed_2538_, v_b_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v_as_2529_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(lean_object* v_init_2540_, lean_object* v___x_2541_, uint8_t v___x_2542_, lean_object* v_n_2543_, lean_object* v_b_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
if (lean_obj_tag(v_n_2543_) == 0)
{
lean_object* v_cs_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; size_t v_sz_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v_cs_2548_ = lean_ctor_get(v_n_2543_, 0);
v___x_2549_ = lean_box(0);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v_b_2544_);
v_sz_2551_ = lean_array_size(v_cs_2548_);
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_2540_, v___x_2541_, v___x_2542_, v_cs_2548_, v_sz_2551_, v___x_2552_, v___x_2550_, v___y_2545_, v___y_2546_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2568_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2568_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2568_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v_fst_2558_; 
v_fst_2558_ = lean_ctor_get(v_a_2554_, 0);
if (lean_obj_tag(v_fst_2558_) == 0)
{
lean_object* v_snd_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v_snd_2559_ = lean_ctor_get(v_a_2554_, 1);
lean_inc(v_snd_2559_);
lean_dec(v_a_2554_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_snd_2559_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2560_);
v___x_2562_ = v___x_2556_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
else
{
lean_object* v_val_2564_; lean_object* v___x_2566_; 
lean_inc_ref(v_fst_2558_);
lean_dec(v_a_2554_);
v_val_2564_ = lean_ctor_get(v_fst_2558_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v_fst_2558_, 1);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_val_2564_);
v___x_2566_ = v___x_2556_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_val_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
v_a_2569_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2553_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2553_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_vs_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; size_t v_sz_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v_vs_2577_ = lean_ctor_get(v_n_2543_, 0);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v_b_2544_);
v_sz_2580_ = lean_array_size(v_vs_2577_);
v___x_2581_ = ((size_t)0ULL);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_2541_, v___x_2542_, v_vs_2577_, v_sz_2580_, v___x_2581_, v___x_2579_, v___y_2545_, v___y_2546_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2597_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2597_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2597_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_fst_2587_; 
v_fst_2587_ = lean_ctor_get(v_a_2583_, 0);
if (lean_obj_tag(v_fst_2587_) == 0)
{
lean_object* v_snd_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
v_snd_2588_ = lean_ctor_get(v_a_2583_, 1);
lean_inc(v_snd_2588_);
lean_dec(v_a_2583_);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_snd_2588_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2589_);
v___x_2591_ = v___x_2585_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
else
{
lean_object* v_val_2593_; lean_object* v___x_2595_; 
lean_inc_ref(v_fst_2587_);
lean_dec(v_a_2583_);
v_val_2593_ = lean_ctor_get(v_fst_2587_, 0);
lean_inc(v_val_2593_);
lean_dec_ref_known(v_fst_2587_, 1);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v_val_2593_);
v___x_2595_ = v___x_2585_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_val_2593_);
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
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_a_2598_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2582_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2582_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(lean_object* v_init_2606_, lean_object* v___x_2607_, uint8_t v___x_2608_, lean_object* v_as_2609_, size_t v_sz_2610_, size_t v_i_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_usize_dec_lt(v_i_2611_, v_sz_2610_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref(v___x_2607_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_b_2612_);
return v___x_2617_;
}
else
{
lean_object* v_snd_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2652_; 
v_snd_2618_ = lean_ctor_get(v_b_2612_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_b_2612_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v_b_2612_, 0);
lean_dec(v_unused_2653_);
v___x_2620_ = v_b_2612_;
v_isShared_2621_ = v_isSharedCheck_2652_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_snd_2618_);
lean_dec(v_b_2612_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2652_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v_a_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_box(0);
v_a_2623_ = lean_array_uget_borrowed(v_as_2609_, v_i_2611_);
lean_inc(v_snd_2618_);
lean_inc_ref(v___x_2607_);
v___x_2624_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2606_, v___x_2607_, v___x_2608_, v_a_2623_, v_snd_2618_, v___y_2613_, v___y_2614_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2643_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2643_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2643_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
if (lean_obj_tag(v_a_2625_) == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
lean_dec_ref(v___x_2607_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_a_2625_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2629_);
v___x_2631_ = v___x_2620_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_snd_2618_);
v___x_2631_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2631_);
v___x_2633_ = v___x_2627_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; 
lean_del_object(v___x_2627_);
lean_dec(v_snd_2618_);
v_a_2636_ = lean_ctor_get(v_a_2625_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v_a_2625_, 1);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v_a_2636_);
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2638_ = v___x_2620_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_a_2636_);
v___x_2638_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
size_t v___x_2639_; size_t v___x_2640_; 
v___x_2639_ = ((size_t)1ULL);
v___x_2640_ = lean_usize_add(v_i_2611_, v___x_2639_);
v_i_2611_ = v___x_2640_;
v_b_2612_ = v___x_2638_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_del_object(v___x_2620_);
lean_dec(v_snd_2618_);
lean_dec_ref(v___x_2607_);
v_a_2644_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2624_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2624_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11___boxed(lean_object* v_init_2654_, lean_object* v___x_2655_, lean_object* v___x_2656_, lean_object* v_as_2657_, lean_object* v_sz_2658_, lean_object* v_i_2659_, lean_object* v_b_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v___x_12595__boxed_2664_; size_t v_sz_boxed_2665_; size_t v_i_boxed_2666_; lean_object* v_res_2667_; 
v___x_12595__boxed_2664_ = lean_unbox(v___x_2656_);
v_sz_boxed_2665_ = lean_unbox_usize(v_sz_2658_);
lean_dec(v_sz_2658_);
v_i_boxed_2666_ = lean_unbox_usize(v_i_2659_);
lean_dec(v_i_2659_);
v_res_2667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_2654_, v___x_2655_, v___x_12595__boxed_2664_, v_as_2657_, v_sz_boxed_2665_, v_i_boxed_2666_, v_b_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec_ref(v_as_2657_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8___boxed(lean_object* v_init_2668_, lean_object* v___x_2669_, lean_object* v___x_2670_, lean_object* v_n_2671_, lean_object* v_b_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
uint8_t v___x_12616__boxed_2676_; lean_object* v_res_2677_; 
v___x_12616__boxed_2676_ = lean_unbox(v___x_2670_);
v_res_2677_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2668_, v___x_2669_, v___x_12616__boxed_2676_, v_n_2671_, v_b_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_n_2671_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(lean_object* v___x_2678_, uint8_t v___x_2679_, lean_object* v_as_2680_, size_t v_sz_2681_, size_t v_i_2682_, lean_object* v_b_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_usize_dec_lt(v_i_2682_, v_sz_2681_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec_ref(v___x_2678_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_b_2683_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; lean_object* v_a_2691_; lean_object* v___x_2696_; lean_object* v_a_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
lean_dec_ref(v_b_2683_);
v___x_2689_ = lean_box(0);
v___x_2696_ = lean_box(0);
v_a_2697_ = lean_array_uget_borrowed(v_as_2680_, v_i_2682_);
lean_inc_ref(v___x_2678_);
lean_inc(v_a_2697_);
v___x_2698_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2697_, v___x_2678_);
v___x_2699_ = lean_box(0);
v___x_2700_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2679_, v___x_2698_, v___x_2699_);
v___x_2701_ = l_List_isEmpty___redArg(v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___f_2702_; lean_object* v___x_2703_; 
v___f_2702_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2702_, 0, v___x_2700_);
lean_closure_set(v___f_2702_, 1, v___x_2696_);
v___x_2703_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2702_, v___y_2684_, v___y_2685_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_dec_ref_known(v___x_2703_, 1);
v_a_2691_ = v___x_2696_;
goto v___jp_2690_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v___x_2678_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_dec(v___x_2700_);
v_a_2691_ = v___x_2696_;
goto v___jp_2690_;
}
v___jp_2690_:
{
lean_object* v___x_2692_; size_t v___x_2693_; size_t v___x_2694_; 
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2689_);
lean_ctor_set(v___x_2692_, 1, v_a_2691_);
v___x_2693_ = ((size_t)1ULL);
v___x_2694_ = lean_usize_add(v_i_2682_, v___x_2693_);
v_i_2682_ = v___x_2694_;
v_b_2683_ = v___x_2692_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14___boxed(lean_object* v___x_2712_, lean_object* v___x_2713_, lean_object* v_as_2714_, lean_object* v_sz_2715_, lean_object* v_i_2716_, lean_object* v_b_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
uint8_t v___x_12802__boxed_2721_; size_t v_sz_boxed_2722_; size_t v_i_boxed_2723_; lean_object* v_res_2724_; 
v___x_12802__boxed_2721_ = lean_unbox(v___x_2713_);
v_sz_boxed_2722_ = lean_unbox_usize(v_sz_2715_);
lean_dec(v_sz_2715_);
v_i_boxed_2723_ = lean_unbox_usize(v_i_2716_);
lean_dec(v_i_2716_);
v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_2712_, v___x_12802__boxed_2721_, v_as_2714_, v_sz_boxed_2722_, v_i_boxed_2723_, v_b_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v_as_2714_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(lean_object* v___x_2728_, uint8_t v___x_2729_, lean_object* v_as_2730_, size_t v_sz_2731_, size_t v_i_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_usize_dec_lt(v_i_2732_, v_sz_2731_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
lean_dec_ref(v___x_2728_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_b_2733_);
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
lean_dec_ref(v_b_2733_);
v___x_2739_ = lean_box(0);
v_a_2745_ = lean_array_uget_borrowed(v_as_2730_, v_i_2732_);
lean_inc_ref(v___x_2728_);
lean_inc(v_a_2745_);
v___x_2746_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2745_, v___x_2728_);
v___x_2747_ = lean_box(0);
v___x_2748_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2729_, v___x_2746_, v___x_2747_);
v___x_2749_ = l_List_isEmpty___redArg(v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___f_2750_; lean_object* v___x_2751_; 
v___f_2750_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2750_, 0, v___x_2748_);
lean_closure_set(v___f_2750_, 1, v___x_2739_);
v___x_2751_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2750_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_dec_ref_known(v___x_2751_, 1);
goto v___jp_2740_;
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref(v___x_2728_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_dec(v___x_2748_);
goto v___jp_2740_;
}
v___jp_2740_:
{
lean_object* v___x_2741_; size_t v___x_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v___x_2741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0));
v___x_2742_ = ((size_t)1ULL);
v___x_2743_ = lean_usize_add(v_i_2732_, v___x_2742_);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_2728_, v___x_2729_, v_as_2730_, v_sz_2731_, v___x_2743_, v___x_2741_, v___y_2734_, v___y_2735_);
return v___x_2744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___boxed(lean_object* v___x_2760_, lean_object* v___x_2761_, lean_object* v_as_2762_, lean_object* v_sz_2763_, lean_object* v_i_2764_, lean_object* v_b_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
uint8_t v___x_12872__boxed_2769_; size_t v_sz_boxed_2770_; size_t v_i_boxed_2771_; lean_object* v_res_2772_; 
v___x_12872__boxed_2769_ = lean_unbox(v___x_2761_);
v_sz_boxed_2770_ = lean_unbox_usize(v_sz_2763_);
lean_dec(v_sz_2763_);
v_i_boxed_2771_ = lean_unbox_usize(v_i_2764_);
lean_dec(v_i_2764_);
v_res_2772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_2760_, v___x_12872__boxed_2769_, v_as_2762_, v_sz_boxed_2770_, v_i_boxed_2771_, v_b_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec_ref(v_as_2762_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(lean_object* v___x_2773_, uint8_t v___x_2774_, lean_object* v_t_2775_, lean_object* v_init_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_root_2780_; lean_object* v_tail_2781_; lean_object* v___x_2782_; 
v_root_2780_ = lean_ctor_get(v_t_2775_, 0);
v_tail_2781_ = lean_ctor_get(v_t_2775_, 1);
lean_inc_ref(v___x_2773_);
v___x_2782_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2776_, v___x_2773_, v___x_2774_, v_root_2780_, v_init_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2819_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2819_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2819_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
if (lean_obj_tag(v_a_2783_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; 
lean_dec_ref(v___x_2773_);
v_a_2787_ = lean_ctor_get(v_a_2783_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v_a_2783_, 1);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v_a_2787_);
v___x_2789_ = v___x_2785_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; size_t v_sz_2794_; size_t v___x_2795_; lean_object* v___x_2796_; 
lean_del_object(v___x_2785_);
v_a_2791_ = lean_ctor_get(v_a_2783_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v_a_2783_, 1);
v___x_2792_ = lean_box(0);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v_a_2791_);
v_sz_2794_ = lean_array_size(v_tail_2781_);
v___x_2795_ = ((size_t)0ULL);
v___x_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_2773_, v___x_2774_, v_tail_2781_, v_sz_2794_, v___x_2795_, v___x_2793_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2810_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2810_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2810_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v_fst_2801_; 
v_fst_2801_ = lean_ctor_get(v_a_2797_, 0);
if (lean_obj_tag(v_fst_2801_) == 0)
{
lean_object* v_snd_2802_; lean_object* v___x_2804_; 
v_snd_2802_ = lean_ctor_get(v_a_2797_, 1);
lean_inc(v_snd_2802_);
lean_dec(v_a_2797_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v_snd_2802_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_snd_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
else
{
lean_object* v_val_2806_; lean_object* v___x_2808_; 
lean_inc_ref(v_fst_2801_);
lean_dec(v_a_2797_);
v_val_2806_ = lean_ctor_get(v_fst_2801_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v_fst_2801_, 1);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v_val_2806_);
v___x_2808_ = v___x_2799_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_val_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
v_a_2811_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2796_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2796_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v___x_2773_);
v_a_2820_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2782_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2782_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5___boxed(lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v_t_2830_, lean_object* v_init_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
uint8_t v___x_12935__boxed_2835_; lean_object* v_res_2836_; 
v___x_12935__boxed_2835_ = lean_unbox(v___x_2829_);
v_res_2836_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v___x_2828_, v___x_12935__boxed_2835_, v_t_2830_, v_init_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec_ref(v_t_2830_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(lean_object* v_o_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_env_2842_; lean_object* v___x_2843_; lean_object* v_toEnvExtension_2844_; lean_object* v_asyncMode_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v_merged_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
v___x_2840_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2841_ = lean_st_ref_get(v___y_2838_);
v_env_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc_ref(v_env_2842_);
lean_dec(v___x_2841_);
v___x_2843_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2844_ = lean_ctor_get(v___x_2843_, 0);
v_asyncMode_2845_ = lean_ctor_get(v_toEnvExtension_2844_, 2);
v___x_2846_ = lean_box(0);
v___x_2847_ = 0;
v___x_2848_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2840_, v___x_2843_, v_env_2842_, v_asyncMode_2845_, v___x_2846_, v___x_2847_);
v_merged_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v___x_2848_, 1);
lean_dec(v_unused_2858_);
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_merged_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_merged_2849_);
lean_ctor_set(v___x_2851_, 0, v_o_2837_);
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_o_2837_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_merged_2849_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_2859_, v___y_2860_);
lean_dec(v___y_2860_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_scopes_2868_; lean_object* v___x_2869_; lean_object* v_opts_2870_; lean_object* v___x_2871_; 
v___x_2866_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2867_ = lean_st_ref_get(v___y_2864_);
v_scopes_2868_ = lean_ctor_get(v___x_2867_, 2);
lean_inc(v_scopes_2868_);
lean_dec(v___x_2867_);
v___x_2869_ = l_List_head_x21___redArg(v___x_2866_, v_scopes_2868_);
lean_dec(v_scopes_2868_);
v_opts_2870_ = lean_ctor_get(v___x_2869_, 1);
lean_inc_ref(v_opts_2870_);
lean_dec(v___x_2869_);
v___x_2871_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_opts_2870_, v___y_2864_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0___boxed(lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(lean_object* v_x_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2914_; 
v___x_2880_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_2877_, v___y_2878_);
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2883_ = v___x_2880_;
v_isShared_2884_ = v_isSharedCheck_2914_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2914_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2885_ = lean_st_ref_get(v___y_2878_);
v___x_2891_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
v___x_2892_ = l_Lean_Linter_getLinterValue(v___x_2891_, v_a_2881_);
lean_dec(v_a_2881_);
if (v___x_2892_ == 0)
{
lean_dec(v___x_2885_);
goto v___jp_2886_;
}
else
{
lean_object* v_infoState_2893_; uint8_t v_enabled_2894_; 
v_infoState_2893_ = lean_ctor_get(v___x_2885_, 8);
lean_inc_ref(v_infoState_2893_);
lean_dec(v___x_2885_);
v_enabled_2894_ = lean_ctor_get_uint8(v_infoState_2893_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2893_);
if (v_enabled_2894_ == 0)
{
goto v___jp_2886_;
}
else
{
lean_object* v___x_2895_; lean_object* v_messages_2896_; uint8_t v___x_2897_; 
lean_del_object(v___x_2883_);
v___x_2895_ = lean_st_ref_get(v___y_2878_);
v_messages_2896_ = lean_ctor_get(v___x_2895_, 1);
lean_inc_ref(v_messages_2896_);
lean_dec(v___x_2895_);
v___x_2897_ = l_Lean_MessageLog_hasErrors(v_messages_2896_);
lean_dec_ref(v_messages_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v_env_2899_; lean_object* v___x_2900_; lean_object* v_a_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2898_ = lean_st_ref_get(v___y_2878_);
v_env_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_env_2899_);
lean_dec(v___x_2898_);
v___x_2900_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_2878_);
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref(v___x_2900_);
v___x_2902_ = lean_box(0);
v___x_2903_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v_env_2899_, v___x_2897_, v_a_2901_, v___x_2902_, v___y_2877_, v___y_2878_);
lean_dec(v_a_2901_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2903_, 0);
lean_dec(v_unused_2911_);
v___x_2905_ = v___x_2903_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_dec(v___x_2903_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2902_);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2902_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
else
{
return v___x_2903_;
}
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
}
}
v___jp_2886_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = lean_box(0);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2887_);
v___x_2889_ = v___x_2883_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0___boxed(lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(v_x_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v_x_2915_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(lean_object* v_o_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_2935_, v___y_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___boxed(lean_object* v_o_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(v_o_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(lean_object* v_as_2945_, lean_object* v_as_x27_2946_, lean_object* v_b_2947_, lean_object* v_a_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_2946_, v_b_2947_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___boxed(lean_object* v_as_2957_, lean_object* v_as_x27_2958_, lean_object* v_b_2959_, lean_object* v_a_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(v_as_2957_, v_as_x27_2958_, v_b_2959_, v_a_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v_as_x27_2958_);
lean_dec(v_as_2957_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(lean_object* v_o_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_o_2969_, v___y_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_o_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(v_o_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(lean_object* v_ref_2987_, lean_object* v_msgData_2988_, uint8_t v_severity_2989_, uint8_t v_isSilent_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2987_, v_msgData_2988_, v_severity_2989_, v_isSilent_2990_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_ref_2999_, lean_object* v_msgData_3000_, lean_object* v_severity_3001_, lean_object* v_isSilent_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
uint8_t v_severity_boxed_3010_; uint8_t v_isSilent_boxed_3011_; lean_object* v_res_3012_; 
v_severity_boxed_3010_ = lean_unbox(v_severity_3001_);
v_isSilent_boxed_3011_ = lean_unbox(v_isSilent_3002_);
v_res_3012_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(v_ref_2999_, v_msgData_3000_, v_severity_boxed_3010_, v_isSilent_boxed_3011_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v_ref_2999_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = ((lean_object*)(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter));
v___x_3015_ = l_Lean_Elab_Command_addLinter(v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2____boxed(lean_object* v_a_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
return v_res_3017_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrivateName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
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
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
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
res = initialize_Lean_Elab_InfoTree_Util(builtin);
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
