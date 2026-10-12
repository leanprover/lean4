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
uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(lean_object* v_p_1_, lean_object* v_type_2_){
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
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1_ = stack[0].m_obj;
lean_object* v_type_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(v_p_1_, v_type_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP___boxed(lean_object* v_p_12_, lean_object* v_type_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(v_p_12_, v_type_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(lean_object* v_p_16_, lean_object* v_e_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Expr_cleanupAnnotations(v_e_17_);
switch(lean_obj_tag(v___x_18_))
{
case 7:
{
lean_object* v_binderType_19_; lean_object* v_body_20_; uint8_t v_binderInfo_21_; uint8_t v___y_23_; uint8_t v___x_25_; 
v_binderType_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc_ref(v_binderType_19_);
v_body_20_ = lean_ctor_get(v___x_18_, 2);
lean_inc_ref(v_body_20_);
v_binderInfo_21_ = lean_ctor_get_uint8(v___x_18_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_18_, 3);
v___x_25_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_21_);
if (v___x_25_ == 0)
{
lean_dec_ref(v_binderType_19_);
v___y_23_ = v___x_25_;
goto v___jp_22_;
}
else
{
lean_object* v___x_26_; uint8_t v___x_27_; 
lean_inc_ref(v_p_16_);
v___x_26_ = lean_apply_1(v_p_16_, v_binderType_19_);
v___x_27_ = lean_unbox(v___x_26_);
v___y_23_ = v___x_27_;
goto v___jp_22_;
}
v___jp_22_:
{
if (v___y_23_ == 0)
{
v_e_17_ = v_body_20_;
goto _start;
}
else
{
lean_dec_ref(v_body_20_);
lean_dec_ref(v_p_16_);
return v___y_23_;
}
}
}
case 8:
{
lean_object* v_body_28_; 
v_body_28_ = lean_ctor_get(v___x_18_, 3);
lean_inc_ref(v_body_28_);
lean_dec_ref_known(v___x_18_, 4);
v_e_17_ = v_body_28_;
goto _start;
}
default: 
{
uint8_t v___x_30_; 
lean_dec_ref(v___x_18_);
lean_dec_ref(v_p_16_);
v___x_30_ = 0;
return v___x_30_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_16_ = stack[0].m_obj;
lean_object* v_e_17_ = stack[1].m_obj;
uint8_t v_res_31_;
v_res_31_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(v_p_16_, v_e_17_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf___boxed(lean_object* v_p_32_, lean_object* v_e_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(v_p_32_, v_e_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(lean_object* v_p_36_, lean_object* v_body_37_, lean_object* v_current_38_, lean_object* v_acc_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Expr_cleanupAnnotations(v_body_37_);
switch(lean_obj_tag(v___x_40_))
{
case 7:
{
lean_object* v_binderType_41_; lean_object* v_body_42_; uint8_t v_binderInfo_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___y_47_; uint8_t v___x_54_; 
v_binderType_41_ = lean_ctor_get(v___x_40_, 1);
lean_inc_ref(v_binderType_41_);
v_body_42_ = lean_ctor_get(v___x_40_, 2);
lean_inc_ref(v_body_42_);
v_binderInfo_43_ = lean_ctor_get_uint8(v___x_40_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_40_, 3);
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_current_38_, v___x_44_);
v___x_54_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_43_);
if (v___x_54_ == 0)
{
lean_dec_ref(v_binderType_41_);
v___y_47_ = v___x_54_;
goto v___jp_46_;
}
else
{
lean_object* v___x_55_; uint8_t v___x_56_; 
lean_inc_ref(v_p_36_);
v___x_55_ = lean_apply_1(v_p_36_, v_binderType_41_);
v___x_56_ = lean_unbox(v___x_55_);
v___y_47_ = v___x_56_;
goto v___jp_46_;
}
v___jp_46_:
{
if (v___y_47_ == 0)
{
lean_dec(v_current_38_);
v_body_37_ = v_body_42_;
v_current_38_ = v___x_45_;
goto _start;
}
else
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_expr_has_loose_bvar(v_body_42_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
v___x_51_ = lean_array_push(v_acc_39_, v_current_38_);
v_body_37_ = v_body_42_;
v_current_38_ = v___x_45_;
v_acc_39_ = v___x_51_;
goto _start;
}
else
{
lean_dec(v_current_38_);
v_body_37_ = v_body_42_;
v_current_38_ = v___x_45_;
goto _start;
}
}
}
}
case 8:
{
lean_object* v_body_57_; 
v_body_57_ = lean_ctor_get(v___x_40_, 3);
lean_inc_ref(v_body_57_);
lean_dec_ref_known(v___x_40_, 4);
v_body_37_ = v_body_57_;
goto _start;
}
default: 
{
lean_dec_ref(v___x_40_);
lean_dec(v_current_38_);
lean_dec_ref(v_p_36_);
return v_acc_39_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(lean_object* v_p_61_, lean_object* v_e_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0));
v___x_65_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(v_p_61_, v_e_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(lean_object* v_env_66_, lean_object* v_p_67_, lean_object* v_decl_68_, uint8_t v_skipRealize_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Environment_findAsync_x3f(v_env_66_, v_decl_68_, v_skipRealize_69_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v___x_71_; 
lean_dec_ref(v_p_67_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_85_; 
v_val_72_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_85_ == 0)
{
v___x_74_ = v___x_70_;
v_isShared_75_ = v_isSharedCheck_85_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v___x_70_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_85_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint8_t v_kind_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_kind_76_ = lean_ctor_get_uint8(v_val_72_, sizeof(void*)*3);
v___x_77_ = lean_box(v_kind_76_);
v___x_78_ = lean_apply_1(v_p_67_, v___x_77_);
v___x_79_ = lean_unbox(v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_del_object(v___x_74_);
lean_dec(v_val_72_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = l_Lean_AsyncConstantInfo_toConstantVal(v_val_72_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_81_);
v___x_83_ = v___x_74_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_66_ = stack[0].m_obj;
lean_object* v_p_67_ = stack[1].m_obj;
lean_object* v_decl_68_ = stack[2].m_obj;
uint8_t v_skipRealize_69_ = stack[3].m_num;
lean_object* v_res_86_;
v_res_86_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_66_, v_p_67_, v_decl_68_, v_skipRealize_69_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f___boxed(lean_object* v_env_87_, lean_object* v_p_88_, lean_object* v_decl_89_, lean_object* v_skipRealize_90_){
_start:
{
uint8_t v_skipRealize_boxed_91_; lean_object* v_res_92_; 
v_skipRealize_boxed_91_ = lean_unbox(v_skipRealize_90_);
v_res_92_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_87_, v_p_88_, v_decl_89_, v_skipRealize_boxed_91_);
return v_res_92_;
}
}
uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(uint8_t v_x_93_){
_start:
{
if (v_x_93_ == 1)
{
uint8_t v___x_94_; 
v___x_94_ = 1;
return v___x_94_;
}
else
{
uint8_t v___x_95_; 
v___x_95_ = 0;
return v___x_95_;
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_93_ = stack[0].m_num;
uint8_t v_res_96_;
v_res_96_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(v_x_93_);
stack->m_num = v_res_96_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0___boxed(lean_object* v_x_97_){
_start:
{
uint8_t v_x_22__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_x_22__boxed_98_ = lean_unbox(v_x_97_);
v_res_99_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(v_x_22__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(lean_object* v_env_102_, lean_object* v_decl_103_, uint8_t v_skipRealize_104_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; 
v___f_105_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0));
v___x_106_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_102_, v___f_105_, v_decl_103_, v_skipRealize_104_);
return v___x_106_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_102_ = stack[0].m_obj;
lean_object* v_decl_103_ = stack[1].m_obj;
uint8_t v_skipRealize_104_ = stack[2].m_num;
lean_object* v_res_107_;
v_res_107_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_102_, v_decl_103_, v_skipRealize_104_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___boxed(lean_object* v_env_108_, lean_object* v_decl_109_, lean_object* v_skipRealize_110_){
_start:
{
uint8_t v_skipRealize_boxed_111_; lean_object* v_res_112_; 
v_skipRealize_boxed_111_ = lean_unbox(v_skipRealize_110_);
v_res_112_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_108_, v_decl_109_, v_skipRealize_boxed_111_);
return v_res_112_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(lean_object* v_name_113_, lean_object* v_decl_114_, lean_object* v_ref_115_){
_start:
{
lean_object* v_defValue_117_; lean_object* v_descr_118_; lean_object* v_deprecation_x3f_119_; lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_defValue_117_ = lean_ctor_get(v_decl_114_, 0);
v_descr_118_ = lean_ctor_get(v_decl_114_, 1);
v_deprecation_x3f_119_ = lean_ctor_get(v_decl_114_, 2);
v___x_120_ = lean_alloc_ctor(1, 0, 1);
v___x_121_ = lean_unbox(v_defValue_117_);
lean_ctor_set_uint8(v___x_120_, 0, v___x_121_);
lean_inc(v_deprecation_x3f_119_);
lean_inc_ref(v_descr_118_);
lean_inc_n(v_name_113_, 2);
v___x_122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_122_, 0, v_name_113_);
lean_ctor_set(v___x_122_, 1, v_ref_115_);
lean_ctor_set(v___x_122_, 2, v___x_120_);
lean_ctor_set(v___x_122_, 3, v_descr_118_);
lean_ctor_set(v___x_122_, 4, v_deprecation_x3f_119_);
v___x_123_ = lean_register_option(v_name_113_, v___x_122_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_123_, 0);
lean_dec(v_unused_132_);
v___x_125_ = v___x_123_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_dec(v___x_123_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
lean_inc(v_defValue_117_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_name_113_);
lean_ctor_set(v___x_127_, 1, v_defValue_117_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec(v_name_113_);
v_a_133_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_123_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_123_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_113_ = stack[0].m_obj;
lean_object* v_decl_114_ = stack[1].m_obj;
lean_object* v_ref_115_ = stack[2].m_obj;
lean_object* v_res_141_;
v_res_141_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v_name_113_, v_decl_114_, v_ref_115_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_142_, lean_object* v_decl_143_, lean_object* v_ref_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v_name_142_, v_decl_143_, v_ref_144_);
lean_dec_ref(v_decl_143_);
return v_res_146_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_172_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_173_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_));
v___x_174_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v___x_171_, v___x_172_, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_175_;
v_res_175_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4____boxed(lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
return v_res_177_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2));
v___x_183_ = l_Lean_stringToMessageData(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4));
v___x_186_ = l_Lean_stringToMessageData(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6));
v___x_189_ = l_Lean_stringToMessageData(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8));
v___x_192_ = l_Lean_stringToMessageData(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0(lean_object* v_param_193_){
_start:
{
lean_object* v_type_x3f_194_; lean_object* v_idx_195_; uint8_t v_appearsInTypeProof_196_; lean_object* v___y_198_; 
v_type_x3f_194_ = lean_ctor_get(v_param_193_, 1);
lean_inc(v_type_x3f_194_);
v_idx_195_ = lean_ctor_get(v_param_193_, 2);
lean_inc(v_idx_195_);
v_appearsInTypeProof_196_ = lean_ctor_get_uint8(v_param_193_, sizeof(void*)*3);
lean_dec_ref(v_param_193_);
if (lean_obj_tag(v_type_x3f_194_) == 1)
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_220_; 
v_val_201_ = lean_ctor_get(v_type_x3f_194_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v_type_x3f_194_);
if (v_isSharedCheck_220_ == 0)
{
v___x_203_ = v_type_x3f_194_;
v_isShared_204_ = v_isSharedCheck_220_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v_type_x3f_194_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_220_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_205_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
v___x_206_ = l_Lean_MessageData_ofExpr(v_val_201_);
v___x_207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
v___x_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_idx_195_, v___x_210_);
lean_dec(v_idx_195_);
v___x_212_ = l_Nat_reprFast(v___x_211_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 3);
lean_ctor_set(v___x_203_, 0, v___x_212_);
v___x_214_ = v___x_203_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_219_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = l_Lean_MessageData_ofFormat(v___x_214_);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_209_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
v___x_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___y_198_ = v___x_218_;
goto v___jp_197_;
}
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v_type_x3f_194_);
v___x_221_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_idx_195_, v___x_222_);
lean_dec(v_idx_195_);
v___x_224_ = l_Nat_reprFast(v___x_223_);
v___x_225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___x_226_ = l_Lean_MessageData_ofFormat(v___x_225_);
v___x_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_221_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___y_198_ = v___x_227_;
goto v___jp_197_;
}
v___jp_197_:
{
if (v_appearsInTypeProof_196_ == 0)
{
return v___y_198_;
}
else
{
lean_object* v___x_199_; lean_object* v_msg_200_; 
v___x_199_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
v_msg_200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_200_, 0, v___y_198_);
lean_ctor_set(v_msg_200_, 1, v___x_199_);
return v_msg_200_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(lean_object* v_as_230_, size_t v_i_231_, size_t v_stop_232_, lean_object* v_b_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_eq(v_i_231_, v_stop_232_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; size_t v___x_237_; size_t v___x_238_; 
v___x_235_ = lean_array_uget_borrowed(v_as_230_, v_i_231_);
lean_inc(v___x_235_);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v_b_233_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_231_, v___x_237_);
v_i_231_ = v___x_238_;
v_b_233_ = v___x_236_;
goto _start;
}
else
{
return v_b_233_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_230_ = stack[0].m_obj;
size_t v_i_231_ = stack[1].m_num;
size_t v_stop_232_ = stack[2].m_num;
lean_object* v_b_233_ = stack[3].m_obj;
lean_object* v_res_240_;
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v_as_230_, v_i_231_, v_stop_232_, v_b_233_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2___boxed(lean_object* v_as_241_, lean_object* v_i_242_, lean_object* v_stop_243_, lean_object* v_b_244_){
_start:
{
size_t v_i_boxed_245_; size_t v_stop_boxed_246_; lean_object* v_res_247_; 
v_i_boxed_245_ = lean_unbox_usize(v_i_242_);
lean_dec(v_i_242_);
v_stop_boxed_246_ = lean_unbox_usize(v_stop_243_);
lean_dec(v_stop_243_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v_as_241_, v_i_boxed_245_, v_stop_boxed_246_, v_b_244_);
lean_dec_ref(v_as_241_);
return v_res_247_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(lean_object* v_as_248_, size_t v_i_249_, size_t v_stop_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = lean_usize_dec_eq(v_i_249_, v_stop_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; uint8_t v_appearsInTypeProof_253_; 
v___x_252_ = lean_array_uget_borrowed(v_as_248_, v_i_249_);
v_appearsInTypeProof_253_ = lean_ctor_get_uint8(v___x_252_, sizeof(void*)*3);
if (v_appearsInTypeProof_253_ == 0)
{
size_t v___x_254_; size_t v___x_255_; 
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_249_, v___x_254_);
v_i_249_ = v___x_255_;
goto _start;
}
else
{
return v_appearsInTypeProof_253_;
}
}
else
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_248_ = stack[0].m_obj;
size_t v_i_249_ = stack[1].m_num;
size_t v_stop_250_ = stack[2].m_num;
uint8_t v_res_258_;
v_res_258_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_as_248_, v_i_249_, v_stop_250_);
stack->m_num = v_res_258_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3___boxed(lean_object* v_as_259_, lean_object* v_i_260_, lean_object* v_stop_261_){
_start:
{
size_t v_i_boxed_262_; size_t v_stop_boxed_263_; uint8_t v_res_264_; lean_object* v_r_265_; 
v_i_boxed_262_ = lean_unbox_usize(v_i_260_);
lean_dec(v_i_260_);
v_stop_boxed_263_ = lean_unbox_usize(v_stop_261_);
lean_dec(v_stop_261_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_as_259_, v_i_boxed_262_, v_stop_boxed_263_);
lean_dec_ref(v_as_259_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(size_t v_sz_266_, size_t v_i_267_, lean_object* v_bs_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = lean_usize_dec_lt(v_i_267_, v_sz_266_);
if (v___x_269_ == 0)
{
return v_bs_268_;
}
else
{
lean_object* v_v_270_; lean_object* v_type_x3f_271_; lean_object* v_idx_272_; lean_object* v___x_273_; lean_object* v_bs_x27_274_; lean_object* v___y_276_; lean_object* v___y_282_; 
v_v_270_ = lean_array_uget(v_bs_268_, v_i_267_);
v_type_x3f_271_ = lean_ctor_get(v_v_270_, 1);
lean_inc(v_type_x3f_271_);
v_idx_272_ = lean_ctor_get(v_v_270_, 2);
v___x_273_ = lean_unsigned_to_nat(0u);
v_bs_x27_274_ = lean_array_uset(v_bs_268_, v_i_267_, v___x_273_);
if (lean_obj_tag(v_type_x3f_271_) == 1)
{
lean_object* v_val_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_305_; 
v_val_286_ = lean_ctor_get(v_type_x3f_271_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v_type_x3f_271_);
if (v_isSharedCheck_305_ == 0)
{
v___x_288_ = v_type_x3f_271_;
v_isShared_289_ = v_isSharedCheck_305_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_val_286_);
lean_dec(v_type_x3f_271_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_305_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_290_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
v___x_291_ = l_Lean_MessageData_ofExpr(v_val_286_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_idx_272_, v___x_295_);
v___x_297_ = l_Nat_reprFast(v___x_296_);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 3);
lean_ctor_set(v___x_288_, 0, v___x_297_);
v___x_299_ = v___x_288_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_304_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = l_Lean_MessageData_ofFormat(v___x_299_);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_294_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___y_282_ = v___x_303_;
goto v___jp_281_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_type_x3f_271_);
v___x_306_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_idx_272_, v___x_307_);
v___x_309_ = l_Nat_reprFast(v___x_308_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = l_Lean_MessageData_ofFormat(v___x_310_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_306_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___y_282_ = v___x_312_;
goto v___jp_281_;
}
v___jp_275_:
{
size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_267_, v___x_277_);
v___x_279_ = lean_array_uset(v_bs_x27_274_, v_i_267_, v___y_276_);
v_i_267_ = v___x_278_;
v_bs_268_ = v___x_279_;
goto _start;
}
v___jp_281_:
{
uint8_t v_appearsInTypeProof_283_; 
v_appearsInTypeProof_283_ = lean_ctor_get_uint8(v_v_270_, sizeof(void*)*3);
lean_dec(v_v_270_);
if (v_appearsInTypeProof_283_ == 0)
{
v___y_276_ = v___y_282_;
goto v___jp_275_;
}
else
{
lean_object* v___x_284_; lean_object* v_msg_285_; 
v___x_284_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
v_msg_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_285_, 0, v___y_282_);
lean_ctor_set(v_msg_285_, 1, v___x_284_);
v___y_276_ = v_msg_285_;
goto v___jp_275_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_266_ = stack[0].m_num;
size_t v_i_267_ = stack[1].m_num;
lean_object* v_bs_268_ = stack[2].m_obj;
lean_object* v_res_313_;
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_266_, v_i_267_, v_bs_268_);
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0___boxed(lean_object* v_sz_314_, lean_object* v_i_315_, lean_object* v_bs_316_){
_start:
{
size_t v_sz_boxed_317_; size_t v_i_boxed_318_; lean_object* v_res_319_; 
v_sz_boxed_317_ = lean_unbox_usize(v_sz_314_);
lean_dec(v_sz_314_);
v_i_boxed_318_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_boxed_317_, v_i_boxed_318_, v_bs_316_);
return v_res_319_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0));
v___x_322_ = l_Lean_stringToMessageData(v___x_321_);
return v___x_322_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(size_t v_sz_323_, size_t v_i_324_, lean_object* v_bs_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_lt(v_i_324_, v_sz_323_);
if (v___x_326_ == 0)
{
return v_bs_325_;
}
else
{
lean_object* v_v_327_; lean_object* v___x_328_; lean_object* v_bs_x27_329_; lean_object* v___x_330_; lean_object* v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v_v_327_ = lean_array_uget(v_bs_325_, v_i_324_);
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_325_, v_i_324_, v___x_328_);
v___x_330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_v_327_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_324_, v___x_332_);
v___x_334_ = lean_array_uset(v_bs_x27_329_, v_i_324_, v___x_331_);
v_i_324_ = v___x_333_;
v_bs_325_ = v___x_334_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_323_ = stack[0].m_num;
size_t v_i_324_ = stack[1].m_num;
lean_object* v_bs_325_ = stack[2].m_obj;
lean_object* v_res_336_;
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_323_, v_i_324_, v_bs_325_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___boxed(lean_object* v_sz_337_, lean_object* v_i_338_, lean_object* v_bs_339_){
_start:
{
size_t v_sz_boxed_340_; size_t v_i_boxed_341_; lean_object* v_res_342_; 
v_sz_boxed_340_ = lean_unbox_usize(v_sz_337_);
lean_dec(v_sz_337_);
v_i_boxed_341_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_boxed_340_, v_i_boxed_341_, v_bs_339_);
return v_res_342_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(lean_object* v_declName_359_, lean_object* v_unusedInstanceBinders_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___y_363_; lean_object* v___y_364_; size_t v___y_365_; lean_object* v___y_366_; lean_object* v___y_386_; uint8_t v___y_387_; size_t v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; uint8_t v___y_398_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_array_get_size(v_unusedInstanceBinders_360_);
v___x_414_ = lean_nat_dec_lt(v___x_361_, v___x_413_);
if (v___x_414_ == 0)
{
v___y_398_ = v___x_414_;
goto v___jp_397_;
}
else
{
if (v___x_414_ == 0)
{
v___y_398_ = v___x_414_;
goto v___jp_397_;
}
else
{
size_t v___x_415_; size_t v___x_416_; uint8_t v___x_417_; 
v___x_415_ = ((size_t)0ULL);
v___x_416_ = lean_usize_of_nat(v___x_413_);
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_unusedInstanceBinders_360_, v___x_415_, v___x_416_);
v___y_398_ = v___x_417_;
goto v___jp_397_;
}
}
v___jp_362_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; size_t v_sz_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
lean_inc_ref(v___y_366_);
v___x_367_ = l_Lean_stringToMessageData(v___y_366_);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___y_364_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1);
v___x_370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = l_Lean_MessageData_nil;
v_sz_372_ = lean_array_size(v___y_363_);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_372_, v___y_365_, v___y_363_);
v___x_374_ = lean_array_get_size(v___x_373_);
v___x_375_ = lean_nat_dec_lt(v___x_361_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec_ref(v___x_373_);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_370_);
lean_ctor_set(v___x_376_, 1, v___x_371_);
return v___x_376_;
}
else
{
uint8_t v___x_377_; 
v___x_377_ = lean_nat_dec_le(v___x_374_, v___x_374_);
if (v___x_377_ == 0)
{
if (v___x_375_ == 0)
{
lean_object* v___x_378_; 
lean_dec_ref(v___x_373_);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_370_);
lean_ctor_set(v___x_378_, 1, v___x_371_);
return v___x_378_;
}
else
{
size_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_usize_of_nat(v___x_374_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v___x_373_, v___y_365_, v___x_379_, v___x_371_);
lean_dec_ref(v___x_373_);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_370_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
return v___x_381_;
}
}
else
{
size_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_usize_of_nat(v___x_374_);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v___x_373_, v___y_365_, v___x_382_, v___x_371_);
lean_dec_ref(v___x_373_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_370_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
}
}
v___jp_385_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_inc_ref(v___y_390_);
v___x_391_ = l_Lean_stringToMessageData(v___y_390_);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___y_389_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
if (v___y_387_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4));
v___y_363_ = v___y_386_;
v___y_364_ = v___x_394_;
v___y_365_ = v___y_388_;
v___y_366_ = v___x_395_;
goto v___jp_362_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5));
v___y_363_ = v___y_386_;
v___y_364_ = v___x_394_;
v___y_365_ = v___y_388_;
v___y_366_ = v___x_396_;
goto v___jp_362_;
}
}
v___jp_397_:
{
size_t v_sz_399_; size_t v___x_400_; lean_object* v_unusedInstanceBinders_401_; lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_sz_399_ = lean_array_size(v_unusedInstanceBinders_360_);
v___x_400_ = ((size_t)0ULL);
v_unusedInstanceBinders_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_399_, v___x_400_, v_unusedInstanceBinders_360_);
v___x_402_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7);
v___x_403_ = 0;
v___x_404_ = l_Lean_MessageData_ofConstName(v_declName_359_, v___x_403_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_402_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_obj_once(&l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9, &l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9_once, _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_array_get_size(v_unusedInstanceBinders_401_);
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10));
v___y_386_ = v_unusedInstanceBinders_401_;
v___y_387_ = v___y_398_;
v___y_388_ = v___x_400_;
v___y_389_ = v___x_407_;
v___y_390_ = v___x_411_;
goto v___jp_385_;
}
else
{
lean_object* v___x_412_; 
v___x_412_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11));
v___y_386_ = v_unusedInstanceBinders_401_;
v___y_387_ = v___y_398_;
v___y_388_ = v___x_400_;
v___y_389_ = v___x_407_;
v___y_390_ = v___x_412_;
goto v___jp_385_;
}
}
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(lean_object* v_subExpr_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___y_426_; uint8_t v___y_435_; uint8_t v___x_456_; 
v___x_456_ = l_Lean_Expr_hasFVar(v_subExpr_418_);
if (v___x_456_ == 0)
{
v___y_435_ = v___x_456_;
goto v___jp_434_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = l_Lean_Expr_isSorry(v_subExpr_418_);
if (v___x_457_ == 0)
{
v___y_435_ = v___x_456_;
goto v___jp_434_;
}
else
{
uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v_subExpr_418_);
v___x_458_ = 0;
v___x_459_ = lean_box(v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
v___jp_425_:
{
if (lean_obj_tag(v_subExpr_418_) == 1)
{
lean_object* v_fvarId_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v___y_426_);
v_fvarId_427_ = lean_ctor_get(v_subExpr_418_, 0);
lean_inc(v_fvarId_427_);
lean_dec_ref_known(v_subExpr_418_, 1);
v___x_428_ = lean_st_ref_take(v___y_419_);
v___x_429_ = l_Lean_FVarIdSet_insert(v___x_428_, v_fvarId_427_);
v___x_430_ = lean_st_ref_put(v___y_419_, v___x_429_);
v___x_431_ = 0;
v___x_432_ = lean_box(v___x_431_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
else
{
lean_dec_ref(v_subExpr_418_);
return v___y_426_;
}
}
v___jp_434_:
{
if (v___y_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_subExpr_418_);
v___x_436_ = lean_box(v___y_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; 
lean_inc_ref(v_subExpr_418_);
v___x_438_ = l_Lean_Meta_isProof(v_subExpr_418_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_453_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_453_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_453_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___x_443_; 
v___x_443_ = lean_unbox(v_a_439_);
lean_dec(v_a_439_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_box(v___y_435_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_444_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v___y_426_ = v___x_446_;
goto v___jp_425_;
}
}
else
{
uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec_ref(v_subExpr_418_);
v___x_448_ = 0;
v___x_449_ = lean_box(v___x_448_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_449_);
v___x_451_ = v___x_441_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_454_; uint8_t v___x_455_; 
v_a_454_ = lean_ctor_get(v___x_438_, 0);
v___x_455_ = lean_unbox(v_a_454_);
if (v___x_455_ == 0)
{
lean_dec_ref(v_subExpr_418_);
return v___x_438_;
}
else
{
v___y_426_ = v___x_438_;
goto v___jp_425_;
}
}
else
{
lean_dec_ref(v_subExpr_418_);
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_subExpr_418_ = stack[0].m_obj;
lean_object* v___y_419_ = stack[1].m_obj;
lean_object* v___y_420_ = stack[2].m_obj;
lean_object* v___y_421_ = stack[3].m_obj;
lean_object* v___y_422_ = stack[4].m_obj;
lean_object* v___y_423_ = stack[5].m_obj;
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(v_subExpr_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0___boxed(lean_object* v_subExpr_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(v_subExpr_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
return v_res_469_;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_object* v_00_u03b1_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_apply_1(v_x_471_, lean_box(0));
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_471_ = stack[1].m_obj;
lean_object* v___y_472_ = stack[2].m_obj;
lean_object* v___y_473_ = stack[3].m_obj;
lean_object* v___y_474_ = stack[4].m_obj;
lean_object* v___y_475_ = stack[5].m_obj;
lean_object* v___y_476_ = stack[6].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_box(0), v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0___boxed(lean_object* v_00_u03b1_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(v_00_u03b1_481_, v_x_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
return v_res_489_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v_b_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc(v___y_495_);
lean_inc_ref(v___y_494_);
lean_inc(v___y_492_);
lean_inc(v___y_491_);
v___x_499_ = lean_apply_8(v_k_490_, v_b_493_, v___y_491_, v___y_492_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, lean_box(0));
return v___x_499_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_490_ = stack[0].m_obj;
lean_object* v___y_491_ = stack[1].m_obj;
lean_object* v___y_492_ = stack[2].m_obj;
lean_object* v_b_493_ = stack[3].m_obj;
lean_object* v___y_494_ = stack[4].m_obj;
lean_object* v___y_495_ = stack[5].m_obj;
lean_object* v___y_496_ = stack[6].m_obj;
lean_object* v___y_497_ = stack[7].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(v_k_490_, v___y_491_, v___y_492_, v_b_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(v_k_501_, v___y_502_, v___y_503_, v_b_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_503_);
lean_dec(v___y_502_);
return v_res_510_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(lean_object* v_name_511_, uint8_t v_bi_512_, lean_object* v_type_513_, lean_object* v_k_514_, uint8_t v_kind_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___f_523_; lean_object* v___x_524_; 
lean_inc(v___y_517_);
lean_inc(v___y_516_);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_523_, 0, v_k_514_);
lean_closure_set(v___f_523_, 1, v___y_516_);
lean_closure_set(v___f_523_, 2, v___y_517_);
v___x_524_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_511_, v_bi_512_, v_type_513_, v___f_523_, v_kind_515_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_524_) == 0)
{
return v___x_524_;
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_511_ = stack[0].m_obj;
uint8_t v_bi_512_ = stack[1].m_num;
lean_object* v_type_513_ = stack[2].m_obj;
lean_object* v_k_514_ = stack[3].m_obj;
uint8_t v_kind_515_ = stack[4].m_num;
lean_object* v___y_516_ = stack[5].m_obj;
lean_object* v___y_517_ = stack[6].m_obj;
lean_object* v___y_518_ = stack[7].m_obj;
lean_object* v___y_519_ = stack[8].m_obj;
lean_object* v___y_520_ = stack[9].m_obj;
lean_object* v___y_521_ = stack[10].m_obj;
lean_object* v_res_533_;
v_res_533_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_511_, v_bi_512_, v_type_513_, v_k_514_, v_kind_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_534_, lean_object* v_bi_535_, lean_object* v_type_536_, lean_object* v_k_537_, lean_object* v_kind_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint8_t v_bi_boxed_546_; uint8_t v_kind_boxed_547_; lean_object* v_res_548_; 
v_bi_boxed_546_ = lean_unbox(v_bi_535_);
v_kind_boxed_547_ = lean_unbox(v_kind_538_);
v_res_548_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_534_, v_bi_boxed_546_, v_type_536_, v_k_537_, v_kind_boxed_547_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec(v___y_539_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_549_, lean_object* v_f_550_, lean_object* v_body_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(v_fvars_549_, v_f_550_, v_body_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec(v___y_553_);
return v_res_560_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(lean_object* v_f_561_, lean_object* v_fvars_562_, lean_object* v_a_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
if (lean_obj_tag(v_a_563_) == 7)
{
lean_object* v_binderName_571_; lean_object* v_binderType_572_; lean_object* v_body_573_; uint8_t v_binderInfo_574_; lean_object* v___f_575_; lean_object* v_d_576_; lean_object* v___x_577_; 
v_binderName_571_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_binderName_571_);
v_binderType_572_ = lean_ctor_get(v_a_563_, 1);
lean_inc_ref(v_binderType_572_);
v_body_573_ = lean_ctor_get(v_a_563_, 2);
lean_inc_ref(v_body_573_);
v_binderInfo_574_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_563_, 3);
lean_inc_ref(v_f_561_);
lean_inc_ref(v_fvars_562_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed), 11, 3);
lean_closure_set(v___f_575_, 0, v_fvars_562_);
lean_closure_set(v___f_575_, 1, v_f_561_);
lean_closure_set(v___f_575_, 2, v_body_573_);
v_d_576_ = lean_expr_instantiate_rev(v_binderType_572_, v_fvars_562_);
lean_dec_ref(v_fvars_562_);
lean_dec_ref(v_binderType_572_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc(v___y_564_);
lean_inc_ref(v_d_576_);
v___x_577_ = lean_apply_8(v_f_561_, v_d_576_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, lean_box(0));
if (lean_obj_tag(v___x_577_) == 0)
{
uint8_t v___x_578_; lean_object* v___x_579_; 
lean_dec_ref_known(v___x_577_, 1);
v___x_578_ = 0;
v___x_579_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_571_, v_binderInfo_574_, v_d_576_, v___f_575_, v___x_578_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
return v___x_579_;
}
else
{
lean_dec_ref(v_d_576_);
lean_dec_ref(v___f_575_);
lean_dec(v_binderName_571_);
return v___x_577_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_expr_instantiate_rev(v_a_563_, v_fvars_562_);
lean_dec_ref(v_fvars_562_);
lean_dec_ref(v_a_563_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc(v___y_564_);
v___x_581_ = lean_apply_8(v_f_561_, v___x_580_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, lean_box(0));
return v___x_581_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_561_ = stack[0].m_obj;
lean_object* v_fvars_562_ = stack[1].m_obj;
lean_object* v_a_563_ = stack[2].m_obj;
lean_object* v___y_564_ = stack[3].m_obj;
lean_object* v___y_565_ = stack[4].m_obj;
lean_object* v___y_566_ = stack[5].m_obj;
lean_object* v___y_567_ = stack[6].m_obj;
lean_object* v___y_568_ = stack[7].m_obj;
lean_object* v___y_569_ = stack[8].m_obj;
lean_object* v_res_582_;
v_res_582_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_561_, v_fvars_562_, v_a_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
stack->m_obj
 = v_res_582_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(lean_object* v_fvars_583_, lean_object* v_f_584_, lean_object* v_body_585_, lean_object* v_x_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_array_push(v_fvars_583_, v_x_586_);
v___x_595_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_584_, v___x_594_, v_body_585_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_595_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_583_ = stack[0].m_obj;
lean_object* v_f_584_ = stack[1].m_obj;
lean_object* v_body_585_ = stack[2].m_obj;
lean_object* v_x_586_ = stack[3].m_obj;
lean_object* v___y_587_ = stack[4].m_obj;
lean_object* v___y_588_ = stack[5].m_obj;
lean_object* v___y_589_ = stack[6].m_obj;
lean_object* v___y_590_ = stack[7].m_obj;
lean_object* v___y_591_ = stack[8].m_obj;
lean_object* v___y_592_ = stack[9].m_obj;
lean_object* v_res_596_;
v_res_596_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(v_fvars_583_, v_f_584_, v_body_585_, v_x_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_f_597_, lean_object* v_fvars_598_, lean_object* v_a_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_597_, v_fvars_598_, v_a_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec(v___y_600_);
return v_res_607_;
}
}
lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(lean_object* v_f_610_, lean_object* v_e_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_620_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_610_, v___x_619_, v_e_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_620_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_610_ = stack[0].m_obj;
lean_object* v_e_611_ = stack[1].m_obj;
lean_object* v___y_612_ = stack[2].m_obj;
lean_object* v___y_613_ = stack[3].m_obj;
lean_object* v___y_614_ = stack[4].m_obj;
lean_object* v___y_615_ = stack[5].m_obj;
lean_object* v___y_616_ = stack[6].m_obj;
lean_object* v___y_617_ = stack[7].m_obj;
lean_object* v_res_621_;
v_res_621_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v_f_610_, v_e_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___boxed(lean_object* v_f_622_, lean_object* v_e_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v_f_622_, v_e_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec(v___y_624_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
return v_x_632_;
}
else
{
lean_object* v_key_634_; lean_object* v_value_635_; lean_object* v_tail_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_659_; 
v_key_634_ = lean_ctor_get(v_x_633_, 0);
v_value_635_ = lean_ctor_get(v_x_633_, 1);
v_tail_636_ = lean_ctor_get(v_x_633_, 2);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_659_ == 0)
{
v___x_638_ = v_x_633_;
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_tail_636_);
lean_inc(v_value_635_);
lean_inc(v_key_634_);
lean_dec(v_x_633_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_659_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; uint64_t v___x_641_; uint64_t v___x_642_; uint64_t v___x_643_; uint64_t v_fold_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_640_ = lean_array_get_size(v_x_632_);
v___x_641_ = l_Lean_Expr_hash(v_key_634_);
v___x_642_ = 32ULL;
v___x_643_ = lean_uint64_shift_right(v___x_641_, v___x_642_);
v_fold_644_ = lean_uint64_xor(v___x_641_, v___x_643_);
v___x_645_ = 16ULL;
v___x_646_ = lean_uint64_shift_right(v_fold_644_, v___x_645_);
v___x_647_ = lean_uint64_xor(v_fold_644_, v___x_646_);
v___x_648_ = lean_uint64_to_usize(v___x_647_);
v___x_649_ = lean_usize_of_nat(v___x_640_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_sub(v___x_649_, v___x_650_);
v___x_652_ = lean_usize_land(v___x_648_, v___x_651_);
v___x_653_ = lean_array_uget_borrowed(v_x_632_, v___x_652_);
lean_inc(v___x_653_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 2, v___x_653_);
v___x_655_ = v___x_638_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_key_634_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_value_635_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v___x_653_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_array_uset(v_x_632_, v___x_652_, v___x_655_);
v_x_632_ = v___x_656_;
v_x_633_ = v_tail_636_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_i_660_, lean_object* v_source_661_, lean_object* v_target_662_){
_start:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_array_get_size(v_source_661_);
v___x_664_ = lean_nat_dec_lt(v_i_660_, v___x_663_);
if (v___x_664_ == 0)
{
lean_dec_ref(v_source_661_);
lean_dec(v_i_660_);
return v_target_662_;
}
else
{
lean_object* v_es_665_; lean_object* v___x_666_; lean_object* v_source_667_; lean_object* v_target_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_es_665_ = lean_array_fget(v_source_661_, v_i_660_);
v___x_666_ = lean_box(0);
v_source_667_ = lean_array_fset(v_source_661_, v_i_660_, v___x_666_);
v_target_668_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_target_662_, v_es_665_);
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = lean_nat_add(v_i_660_, v___x_669_);
lean_dec(v_i_660_);
v_i_660_ = v___x_670_;
v_source_661_ = v_source_667_;
v_target_662_ = v_target_668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_data_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_nbuckets_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_673_ = lean_array_get_size(v_data_672_);
v___x_674_ = lean_unsigned_to_nat(2u);
v_nbuckets_675_ = lean_nat_mul(v___x_673_, v___x_674_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_box(0);
v___x_678_ = lean_mk_array(v_nbuckets_675_, v___x_677_);
v___x_679_ = lean_array_propagate_mark(v_data_672_, v___x_678_);
v___x_680_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v___x_676_, v_data_672_, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_a_681_, lean_object* v_b_682_, lean_object* v_x_683_){
_start:
{
if (lean_obj_tag(v_x_683_) == 0)
{
lean_dec(v_b_682_);
lean_dec_ref(v_a_681_);
return v_x_683_;
}
else
{
lean_object* v_key_684_; lean_object* v_value_685_; lean_object* v_tail_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_698_; 
v_key_684_ = lean_ctor_get(v_x_683_, 0);
v_value_685_ = lean_ctor_get(v_x_683_, 1);
v_tail_686_ = lean_ctor_get(v_x_683_, 2);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_683_);
if (v_isSharedCheck_698_ == 0)
{
v___x_688_ = v_x_683_;
v_isShared_689_ = v_isSharedCheck_698_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_tail_686_);
lean_inc(v_value_685_);
lean_inc(v_key_684_);
lean_dec(v_x_683_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_698_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
uint8_t v___x_690_; 
v___x_690_ = lean_expr_eqv(v_key_684_, v_a_681_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_681_, v_b_682_, v_tail_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 2, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_key_684_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_value_685_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
lean_object* v___x_696_; 
lean_dec(v_value_685_);
lean_dec(v_key_684_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_b_682_);
lean_ctor_set(v___x_688_, 0, v_a_681_);
v___x_696_ = v___x_688_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_681_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_b_682_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_tail_686_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_a_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
else
{
lean_object* v_key_702_; lean_object* v_tail_703_; uint8_t v___x_704_; 
v_key_702_ = lean_ctor_get(v_x_700_, 0);
v_tail_703_ = lean_ctor_get(v_x_700_, 2);
v___x_704_ = lean_expr_eqv(v_key_702_, v_a_699_);
if (v___x_704_ == 0)
{
v_x_700_ = v_tail_703_;
goto _start;
}
else
{
return v___x_704_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_699_ = stack[0].m_obj;
lean_object* v_x_700_ = stack[1].m_obj;
uint8_t v_res_706_;
v_res_706_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_699_, v_x_700_);
stack->m_num = v_res_706_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_a_707_, lean_object* v_x_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_707_, v_x_708_);
lean_dec(v_x_708_);
lean_dec_ref(v_a_707_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(lean_object* v_m_711_, lean_object* v_a_712_, lean_object* v_b_713_){
_start:
{
lean_object* v_size_714_; lean_object* v_buckets_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_758_; 
v_size_714_ = lean_ctor_get(v_m_711_, 0);
v_buckets_715_ = lean_ctor_get(v_m_711_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_m_711_);
if (v_isSharedCheck_758_ == 0)
{
v___x_717_ = v_m_711_;
v_isShared_718_ = v_isSharedCheck_758_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_buckets_715_);
lean_inc(v_size_714_);
lean_dec(v_m_711_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_758_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; uint64_t v___x_720_; uint64_t v___x_721_; uint64_t v___x_722_; uint64_t v_fold_723_; uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; size_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; lean_object* v_bkt_732_; uint8_t v___x_733_; 
v___x_719_ = lean_array_get_size(v_buckets_715_);
v___x_720_ = l_Lean_Expr_hash(v_a_712_);
v___x_721_ = 32ULL;
v___x_722_ = lean_uint64_shift_right(v___x_720_, v___x_721_);
v_fold_723_ = lean_uint64_xor(v___x_720_, v___x_722_);
v___x_724_ = 16ULL;
v___x_725_ = lean_uint64_shift_right(v_fold_723_, v___x_724_);
v___x_726_ = lean_uint64_xor(v_fold_723_, v___x_725_);
v___x_727_ = lean_uint64_to_usize(v___x_726_);
v___x_728_ = lean_usize_of_nat(v___x_719_);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_sub(v___x_728_, v___x_729_);
v___x_731_ = lean_usize_land(v___x_727_, v___x_730_);
v_bkt_732_ = lean_array_uget_borrowed(v_buckets_715_, v___x_731_);
v___x_733_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_712_, v_bkt_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v_size_x27_735_; lean_object* v___x_736_; lean_object* v_buckets_x27_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_734_ = lean_unsigned_to_nat(1u);
v_size_x27_735_ = lean_nat_add(v_size_714_, v___x_734_);
lean_dec(v_size_714_);
lean_inc(v_bkt_732_);
v___x_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_736_, 0, v_a_712_);
lean_ctor_set(v___x_736_, 1, v_b_713_);
lean_ctor_set(v___x_736_, 2, v_bkt_732_);
v_buckets_x27_737_ = lean_array_uset(v_buckets_715_, v___x_731_, v___x_736_);
v___x_738_ = lean_unsigned_to_nat(4u);
v___x_739_ = lean_nat_mul(v_size_x27_735_, v___x_738_);
v___x_740_ = lean_unsigned_to_nat(3u);
v___x_741_ = lean_nat_div(v___x_739_, v___x_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_array_get_size(v_buckets_x27_737_);
v___x_743_ = lean_nat_dec_le(v___x_741_, v___x_742_);
lean_dec(v___x_741_);
if (v___x_743_ == 0)
{
lean_object* v_val_744_; lean_object* v___x_746_; 
v_val_744_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_buckets_x27_737_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v_val_744_);
lean_ctor_set(v___x_717_, 0, v_size_x27_735_);
v___x_746_ = v___x_717_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_size_x27_735_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_val_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_749_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v_buckets_x27_737_);
lean_ctor_set(v___x_717_, 0, v_size_x27_735_);
v___x_749_ = v___x_717_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_size_x27_735_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_buckets_x27_737_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v___x_751_; lean_object* v_buckets_x27_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
lean_inc(v_bkt_732_);
v___x_751_ = lean_box(0);
v_buckets_x27_752_ = lean_array_uset(v_buckets_715_, v___x_731_, v___x_751_);
v___x_753_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_712_, v_b_713_, v_bkt_732_);
v___x_754_ = lean_array_uset(v_buckets_x27_752_, v___x_731_, v___x_753_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v___x_754_);
v___x_756_ = v___x_717_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_size_714_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(lean_object* v_a_759_, lean_object* v_e_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_763_ = lean_st_ref_take(v_a_759_);
v___x_764_ = lean_box(0);
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v___x_763_, v_e_760_, v_a_761_);
v___x_766_ = lean_st_ref_put(v_a_759_, v___x_765_);
return v___x_764_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_759_ = stack[0].m_obj;
lean_object* v_e_760_ = stack[1].m_obj;
lean_object* v_a_761_ = stack[2].m_obj;
lean_object* v_res_767_;
v_res_767_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(v_a_759_, v_e_760_, v_a_761_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed(lean_object* v_a_768_, lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(v_a_768_, v_e_769_, v_a_770_);
lean_dec(v_a_768_);
return v_res_772_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(lean_object* v_name_773_, lean_object* v_type_774_, lean_object* v_val_775_, lean_object* v_k_776_, uint8_t v_nondep_777_, uint8_t v_kind_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___f_786_; lean_object* v___x_787_; 
lean_inc(v___y_780_);
lean_inc(v___y_779_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_786_, 0, v_k_776_);
lean_closure_set(v___f_786_, 1, v___y_779_);
lean_closure_set(v___f_786_, 2, v___y_780_);
v___x_787_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_773_, v_type_774_, v_val_775_, v___f_786_, v_nondep_777_, v_kind_778_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_787_) == 0)
{
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_773_ = stack[0].m_obj;
lean_object* v_type_774_ = stack[1].m_obj;
lean_object* v_val_775_ = stack[2].m_obj;
lean_object* v_k_776_ = stack[3].m_obj;
uint8_t v_nondep_777_ = stack[4].m_num;
uint8_t v_kind_778_ = stack[5].m_num;
lean_object* v___y_779_ = stack[6].m_obj;
lean_object* v___y_780_ = stack[7].m_obj;
lean_object* v___y_781_ = stack[8].m_obj;
lean_object* v___y_782_ = stack[9].m_obj;
lean_object* v___y_783_ = stack[10].m_obj;
lean_object* v___y_784_ = stack[11].m_obj;
lean_object* v_res_796_;
v_res_796_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_773_, v_type_774_, v_val_775_, v_k_776_, v_nondep_777_, v_kind_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg___boxed(lean_object* v_name_797_, lean_object* v_type_798_, lean_object* v_val_799_, lean_object* v_k_800_, lean_object* v_nondep_801_, lean_object* v_kind_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
uint8_t v_nondep_boxed_810_; uint8_t v_kind_boxed_811_; lean_object* v_res_812_; 
v_nondep_boxed_810_ = lean_unbox(v_nondep_801_);
v_kind_boxed_811_ = lean_unbox(v_kind_802_);
v_res_812_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_797_, v_type_798_, v_val_799_, v_k_800_, v_nondep_boxed_810_, v_kind_boxed_811_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec(v___y_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed(lean_object* v_fvars_813_, lean_object* v_f_814_, lean_object* v_body_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(v_fvars_813_, v_f_814_, v_body_815_, v_x_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec(v___y_817_);
return v_res_824_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(lean_object* v_f_825_, lean_object* v_fvars_826_, lean_object* v_a_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
if (lean_obj_tag(v_a_827_) == 8)
{
lean_object* v_declName_835_; lean_object* v_type_836_; lean_object* v_value_837_; lean_object* v_body_838_; lean_object* v___f_839_; lean_object* v_d_840_; lean_object* v_v_841_; lean_object* v___x_842_; 
v_declName_835_ = lean_ctor_get(v_a_827_, 0);
lean_inc(v_declName_835_);
v_type_836_ = lean_ctor_get(v_a_827_, 1);
lean_inc_ref(v_type_836_);
v_value_837_ = lean_ctor_get(v_a_827_, 2);
lean_inc_ref(v_value_837_);
v_body_838_ = lean_ctor_get(v_a_827_, 3);
lean_inc_ref(v_body_838_);
lean_dec_ref_known(v_a_827_, 4);
lean_inc_ref_n(v_f_825_, 2);
lean_inc_ref(v_fvars_826_);
v___f_839_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed), 11, 3);
lean_closure_set(v___f_839_, 0, v_fvars_826_);
lean_closure_set(v___f_839_, 1, v_f_825_);
lean_closure_set(v___f_839_, 2, v_body_838_);
v_d_840_ = lean_expr_instantiate_rev(v_type_836_, v_fvars_826_);
lean_dec_ref(v_type_836_);
v_v_841_ = lean_expr_instantiate_rev(v_value_837_, v_fvars_826_);
lean_dec_ref(v_fvars_826_);
lean_dec_ref(v_value_837_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v_d_840_);
v___x_842_ = lean_apply_8(v_f_825_, v_d_840_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_843_; 
lean_dec_ref_known(v___x_842_, 1);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc(v___y_828_);
lean_inc_ref(v_v_841_);
v___x_843_ = lean_apply_8(v_f_825_, v_v_841_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
if (lean_obj_tag(v___x_843_) == 0)
{
uint8_t v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; 
lean_dec_ref_known(v___x_843_, 1);
v___x_844_ = 0;
v___x_845_ = 0;
v___x_846_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_declName_835_, v_d_840_, v_v_841_, v___f_839_, v___x_844_, v___x_845_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_846_;
}
else
{
lean_dec_ref(v_v_841_);
lean_dec_ref(v_d_840_);
lean_dec_ref(v___f_839_);
lean_dec(v_declName_835_);
return v___x_843_;
}
}
else
{
lean_dec_ref(v_v_841_);
lean_dec_ref(v_d_840_);
lean_dec_ref(v___f_839_);
lean_dec(v_declName_835_);
lean_dec_ref(v_f_825_);
return v___x_842_;
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_expr_instantiate_rev(v_a_827_, v_fvars_826_);
lean_dec_ref(v_fvars_826_);
lean_dec_ref(v_a_827_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc(v___y_828_);
v___x_848_ = lean_apply_8(v_f_825_, v___x_847_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, lean_box(0));
return v___x_848_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_825_ = stack[0].m_obj;
lean_object* v_fvars_826_ = stack[1].m_obj;
lean_object* v_a_827_ = stack[2].m_obj;
lean_object* v___y_828_ = stack[3].m_obj;
lean_object* v___y_829_ = stack[4].m_obj;
lean_object* v___y_830_ = stack[5].m_obj;
lean_object* v___y_831_ = stack[6].m_obj;
lean_object* v___y_832_ = stack[7].m_obj;
lean_object* v___y_833_ = stack[8].m_obj;
lean_object* v_res_849_;
v_res_849_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_825_, v_fvars_826_, v_a_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
stack->m_obj
 = v_res_849_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(lean_object* v_fvars_850_, lean_object* v_f_851_, lean_object* v_body_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_array_push(v_fvars_850_, v_x_853_);
v___x_862_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_851_, v___x_861_, v_body_852_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_862_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_850_ = stack[0].m_obj;
lean_object* v_f_851_ = stack[1].m_obj;
lean_object* v_body_852_ = stack[2].m_obj;
lean_object* v_x_853_ = stack[3].m_obj;
lean_object* v___y_854_ = stack[4].m_obj;
lean_object* v___y_855_ = stack[5].m_obj;
lean_object* v___y_856_ = stack[6].m_obj;
lean_object* v___y_857_ = stack[7].m_obj;
lean_object* v___y_858_ = stack[8].m_obj;
lean_object* v___y_859_ = stack[9].m_obj;
lean_object* v_res_863_;
v_res_863_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(v_fvars_850_, v_f_851_, v_body_852_, v_x_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___boxed(lean_object* v_f_864_, lean_object* v_fvars_865_, lean_object* v_a_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_864_, v_fvars_865_, v_a_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v___y_867_);
return v_res_874_;
}
}
lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(lean_object* v_f_875_, lean_object* v_e_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_885_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_875_, v___x_884_, v_e_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_885_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_875_ = stack[0].m_obj;
lean_object* v_e_876_ = stack[1].m_obj;
lean_object* v___y_877_ = stack[2].m_obj;
lean_object* v___y_878_ = stack[3].m_obj;
lean_object* v___y_879_ = stack[4].m_obj;
lean_object* v___y_880_ = stack[5].m_obj;
lean_object* v___y_881_ = stack[6].m_obj;
lean_object* v___y_882_ = stack[7].m_obj;
lean_object* v_res_886_;
v_res_886_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v_f_875_, v_e_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
stack->m_obj
 = v_res_886_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5___boxed(lean_object* v_f_887_, lean_object* v_e_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v_f_887_, v_e_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec(v___y_889_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed(lean_object* v_fvars_897_, lean_object* v_f_898_, lean_object* v_body_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(v_fvars_897_, v_f_898_, v_body_899_, v_x_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
return v_res_908_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(lean_object* v_f_909_, lean_object* v_fvars_910_, lean_object* v_a_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
if (lean_obj_tag(v_a_911_) == 6)
{
lean_object* v_binderName_919_; lean_object* v_binderType_920_; lean_object* v_body_921_; uint8_t v_binderInfo_922_; lean_object* v___f_923_; lean_object* v_d_924_; lean_object* v___x_925_; 
v_binderName_919_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v_binderName_919_);
v_binderType_920_ = lean_ctor_get(v_a_911_, 1);
lean_inc_ref(v_binderType_920_);
v_body_921_ = lean_ctor_get(v_a_911_, 2);
lean_inc_ref(v_body_921_);
v_binderInfo_922_ = lean_ctor_get_uint8(v_a_911_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_911_, 3);
lean_inc_ref(v_f_909_);
lean_inc_ref(v_fvars_910_);
v___f_923_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed), 11, 3);
lean_closure_set(v___f_923_, 0, v_fvars_910_);
lean_closure_set(v___f_923_, 1, v_f_909_);
lean_closure_set(v___f_923_, 2, v_body_921_);
v_d_924_ = lean_expr_instantiate_rev(v_binderType_920_, v_fvars_910_);
lean_dec_ref(v_fvars_910_);
lean_dec_ref(v_binderType_920_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
lean_inc(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v_d_924_);
v___x_925_ = lean_apply_8(v_f_909_, v_d_924_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
if (lean_obj_tag(v___x_925_) == 0)
{
uint8_t v___x_926_; lean_object* v___x_927_; 
lean_dec_ref_known(v___x_925_, 1);
v___x_926_ = 0;
v___x_927_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_919_, v_binderInfo_922_, v_d_924_, v___f_923_, v___x_926_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
return v___x_927_;
}
else
{
lean_dec_ref(v_d_924_);
lean_dec_ref(v___f_923_);
lean_dec(v_binderName_919_);
return v___x_925_;
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_expr_instantiate_rev(v_a_911_, v_fvars_910_);
lean_dec_ref(v_fvars_910_);
lean_dec_ref(v_a_911_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
lean_inc(v___y_913_);
lean_inc(v___y_912_);
v___x_929_ = lean_apply_8(v_f_909_, v___x_928_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
return v___x_929_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_909_ = stack[0].m_obj;
lean_object* v_fvars_910_ = stack[1].m_obj;
lean_object* v_a_911_ = stack[2].m_obj;
lean_object* v___y_912_ = stack[3].m_obj;
lean_object* v___y_913_ = stack[4].m_obj;
lean_object* v___y_914_ = stack[5].m_obj;
lean_object* v___y_915_ = stack[6].m_obj;
lean_object* v___y_916_ = stack[7].m_obj;
lean_object* v___y_917_ = stack[8].m_obj;
lean_object* v_res_930_;
v_res_930_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_909_, v_fvars_910_, v_a_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
stack->m_obj
 = v_res_930_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(lean_object* v_fvars_931_, lean_object* v_f_932_, lean_object* v_body_933_, lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_array_push(v_fvars_931_, v_x_934_);
v___x_943_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_932_, v___x_942_, v_body_933_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_943_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_931_ = stack[0].m_obj;
lean_object* v_f_932_ = stack[1].m_obj;
lean_object* v_body_933_ = stack[2].m_obj;
lean_object* v_x_934_ = stack[3].m_obj;
lean_object* v___y_935_ = stack[4].m_obj;
lean_object* v___y_936_ = stack[5].m_obj;
lean_object* v___y_937_ = stack[6].m_obj;
lean_object* v___y_938_ = stack[7].m_obj;
lean_object* v___y_939_ = stack[8].m_obj;
lean_object* v___y_940_ = stack[9].m_obj;
lean_object* v_res_944_;
v_res_944_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(v_fvars_931_, v_f_932_, v_body_933_, v_x_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
stack->m_obj
 = v_res_944_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_f_945_, lean_object* v_fvars_946_, lean_object* v_a_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_945_, v_fvars_946_, v_a_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec(v___y_948_);
return v_res_955_;
}
}
lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(lean_object* v_f_956_, lean_object* v_e_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0));
v___x_966_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_956_, v___x_965_, v_e_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
return v___x_966_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_956_ = stack[0].m_obj;
lean_object* v_e_957_ = stack[1].m_obj;
lean_object* v___y_958_ = stack[2].m_obj;
lean_object* v___y_959_ = stack[3].m_obj;
lean_object* v___y_960_ = stack[4].m_obj;
lean_object* v___y_961_ = stack[5].m_obj;
lean_object* v___y_962_ = stack[6].m_obj;
lean_object* v___y_963_ = stack[7].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v_f_956_, v_e_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4___boxed(lean_object* v_f_968_, lean_object* v_e_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v_f_968_, v_e_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec(v___y_970_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_978_, lean_object* v_x_979_){
_start:
{
if (lean_obj_tag(v_x_979_) == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_box(0);
return v___x_980_;
}
else
{
lean_object* v_key_981_; lean_object* v_value_982_; lean_object* v_tail_983_; uint8_t v___x_984_; 
v_key_981_ = lean_ctor_get(v_x_979_, 0);
v_value_982_ = lean_ctor_get(v_x_979_, 1);
v_tail_983_ = lean_ctor_get(v_x_979_, 2);
v___x_984_ = lean_expr_eqv(v_key_981_, v_a_978_);
if (v___x_984_ == 0)
{
v_x_979_ = v_tail_983_;
goto _start;
}
else
{
lean_object* v___x_986_; 
lean_inc(v_value_982_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_value_982_);
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_987_, lean_object* v_x_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_987_, v_x_988_);
lean_dec(v_x_988_);
lean_dec_ref(v_a_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(lean_object* v_m_990_, lean_object* v_a_991_){
_start:
{
lean_object* v_buckets_992_; lean_object* v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; uint64_t v___x_996_; uint64_t v_fold_997_; uint64_t v___x_998_; uint64_t v___x_999_; uint64_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_buckets_992_ = lean_ctor_get(v_m_990_, 1);
v___x_993_ = lean_array_get_size(v_buckets_992_);
v___x_994_ = l_Lean_Expr_hash(v_a_991_);
v___x_995_ = 32ULL;
v___x_996_ = lean_uint64_shift_right(v___x_994_, v___x_995_);
v_fold_997_ = lean_uint64_xor(v___x_994_, v___x_996_);
v___x_998_ = 16ULL;
v___x_999_ = lean_uint64_shift_right(v_fold_997_, v___x_998_);
v___x_1000_ = lean_uint64_xor(v_fold_997_, v___x_999_);
v___x_1001_ = lean_uint64_to_usize(v___x_1000_);
v___x_1002_ = lean_usize_of_nat(v___x_993_);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_sub(v___x_1002_, v___x_1003_);
v___x_1005_ = lean_usize_land(v___x_1001_, v___x_1004_);
v___x_1006_ = lean_array_uget_borrowed(v_buckets_992_, v___x_1005_);
v___x_1007_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_991_, v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_1008_, v_a_1009_);
lean_dec_ref(v_a_1009_);
lean_dec_ref(v_m_1008_);
return v_res_1010_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_apply_1(v_x_1012_, lean_box(0));
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1012_ = stack[1].m_obj;
lean_object* v___y_1013_ = stack[2].m_obj;
lean_object* v___y_1014_ = stack[3].m_obj;
lean_object* v___y_1015_ = stack[4].m_obj;
lean_object* v___y_1016_ = stack[5].m_obj;
lean_object* v___y_1017_ = stack[6].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_box(0), v_x_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(v_00_u03b1_1022_, v_x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed(lean_object* v_fn_1031_, lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1031_, v_e_1032_, v_a_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec(v_a_1033_);
return v_res_1040_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(lean_object* v_fn_1041_, lean_object* v_e_1042_, lean_object* v_a_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_a_1051_; lean_object* v___y_1063_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_inc(v_a_1043_);
v___x_1065_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1065_, 0, lean_box(0));
lean_closure_set(v___x_1065_, 1, lean_box(0));
lean_closure_set(v___x_1065_, 2, v_a_1043_);
v___x_1066_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_box(0), v___x_1065_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1103_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_a_1067_, v_e_1042_);
lean_dec(v_a_1067_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1072_; 
lean_del_object(v___x_1069_);
lean_inc_ref(v_fn_1041_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc_ref(v_e_1042_);
v___x_1072_ = lean_apply_7(v_fn_1041_, v_e_1042_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; uint8_t v___x_1074_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_unbox(v_a_1073_);
lean_dec(v_a_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec_ref(v_fn_1041_);
v___x_1075_ = lean_box(0);
v_a_1051_ = v___x_1075_;
goto v___jp_1050_;
}
else
{
switch(lean_obj_tag(v_e_1042_))
{
case 7:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1076_, 0, v_fn_1041_);
lean_inc_ref(v_e_1042_);
v___x_1077_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v___x_1076_, v_e_1042_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v___y_1063_ = v___x_1077_;
goto v___jp_1062_;
}
case 6:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1078_, 0, v_fn_1041_);
lean_inc_ref(v_e_1042_);
v___x_1079_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v___x_1078_, v_e_1042_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v___y_1063_ = v___x_1079_;
goto v___jp_1062_;
}
case 8:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed), 9, 1);
lean_closure_set(v___x_1080_, 0, v_fn_1041_);
lean_inc_ref(v_e_1042_);
v___x_1081_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v___x_1080_, v_e_1042_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v___y_1063_ = v___x_1081_;
goto v___jp_1062_;
}
case 5:
{
lean_object* v_fn_1082_; lean_object* v_arg_1083_; lean_object* v___x_1084_; 
v_fn_1082_ = lean_ctor_get(v_e_1042_, 0);
v_arg_1083_ = lean_ctor_get(v_e_1042_, 1);
lean_inc_ref(v_fn_1082_);
lean_inc_ref(v_fn_1041_);
v___x_1084_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1041_, v_fn_1082_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v___x_1085_; 
lean_dec_ref_known(v___x_1084_, 1);
lean_inc_ref(v_arg_1083_);
v___x_1085_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1041_, v_arg_1083_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v___y_1063_ = v___x_1085_;
goto v___jp_1062_;
}
else
{
lean_dec_ref(v_fn_1041_);
v___y_1063_ = v___x_1084_;
goto v___jp_1062_;
}
}
case 10:
{
lean_object* v_expr_1086_; lean_object* v___x_1087_; 
v_expr_1086_ = lean_ctor_get(v_e_1042_, 1);
lean_inc_ref(v_expr_1086_);
v___x_1087_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1041_, v_expr_1086_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v___y_1063_ = v___x_1087_;
goto v___jp_1062_;
}
case 11:
{
lean_object* v_struct_1088_; lean_object* v___x_1089_; 
v_struct_1088_ = lean_ctor_get(v_e_1042_, 2);
lean_inc_ref(v_struct_1088_);
v___x_1089_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1041_, v_struct_1088_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v___y_1063_ = v___x_1089_;
goto v___jp_1062_;
}
default: 
{
lean_object* v___x_1090_; 
lean_dec_ref(v_fn_1041_);
v___x_1090_ = lean_box(0);
v_a_1051_ = v___x_1090_;
goto v___jp_1050_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v_e_1042_);
lean_dec_ref(v_fn_1041_);
v_a_1091_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1072_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1072_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; 
lean_dec_ref(v_e_1042_);
lean_dec_ref(v_fn_1041_);
v_val_1099_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v___x_1071_, 1);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_val_1099_);
v___x_1101_ = v___x_1069_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_val_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_e_1042_);
lean_dec_ref(v_fn_1041_);
v_a_1104_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1066_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1066_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
v___jp_1050_:
{
lean_object* v___f_1052_; lean_object* v___x_1053_; 
lean_inc(v_a_1043_);
v___f_1052_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1052_, 0, v_a_1043_);
lean_closure_set(v___f_1052_, 1, v_e_1042_);
lean_closure_set(v___f_1052_, 2, v_a_1051_);
v___x_1053_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(lean_box(0), v___f_1052_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v___x_1053_, 0);
lean_dec(v_unused_1061_);
v___x_1055_ = v___x_1053_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_dec(v___x_1053_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_a_1051_);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1051_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
return v___x_1053_;
}
}
v___jp_1062_:
{
if (lean_obj_tag(v___y_1063_) == 0)
{
lean_object* v_a_1064_; 
v_a_1064_ = lean_ctor_get(v___y_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___y_1063_, 1);
v_a_1051_ = v_a_1064_;
goto v___jp_1050_;
}
else
{
lean_dec_ref(v_e_1042_);
return v___y_1063_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1041_ = stack[0].m_obj;
lean_object* v_e_1042_ = stack[1].m_obj;
lean_object* v_a_1043_ = stack[2].m_obj;
lean_object* v___y_1044_ = stack[3].m_obj;
lean_object* v___y_1045_ = stack[4].m_obj;
lean_object* v___y_1046_ = stack[5].m_obj;
lean_object* v___y_1047_ = stack[6].m_obj;
lean_object* v___y_1048_ = stack[7].m_obj;
lean_object* v_res_1112_;
v_res_1112_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1041_, v_e_1042_, v_a_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
stack->m_obj
 = v_res_1112_;
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_unsigned_to_nat(16u);
v___x_1115_ = lean_mk_array(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1);
v___x_1120_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1120_, 0, lean_box(0));
lean_closure_set(v___x_1120_, 1, lean_box(0));
lean_closure_set(v___x_1120_, 2, v___x_1119_);
return v___x_1120_;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(lean_object* v_input_1121_, lean_object* v_fn_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_a_1131_; lean_object* v___x_1132_; 
v___x_1129_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2);
v___x_1130_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_box(0), v___x_1129_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1130_);
v___x_1132_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_1122_, v_input_1121_, v_a_1131_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1134_, 0, lean_box(0));
lean_closure_set(v___x_1134_, 1, lean_box(0));
lean_closure_set(v___x_1134_, 2, v_a_1131_);
v___x_1135_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(lean_box(0), v___x_1134_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1143_);
v___x_1137_ = v___x_1135_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1135_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_a_1133_);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1133_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_dec(v_a_1131_);
return v___x_1132_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1121_ = stack[0].m_obj;
lean_object* v_fn_1122_ = stack[1].m_obj;
lean_object* v___y_1123_ = stack[2].m_obj;
lean_object* v___y_1124_ = stack[3].m_obj;
lean_object* v___y_1125_ = stack[4].m_obj;
lean_object* v___y_1126_ = stack[5].m_obj;
lean_object* v___y_1127_ = stack[6].m_obj;
lean_object* v_res_1144_;
v_res_1144_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_input_1121_, v_fn_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1144_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___boxed(lean_object* v_input_1145_, lean_object* v_fn_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_input_1145_, v_fn_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
return v_res_1153_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(lean_object* v_e_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___f_1162_; lean_object* v___x_1163_; 
v___f_1162_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0));
v___x_1163_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_e_1155_, v___f_1162_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
return v___x_1163_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1155_ = stack[0].m_obj;
lean_object* v_a_1156_ = stack[1].m_obj;
lean_object* v_a_1157_ = stack[2].m_obj;
lean_object* v_a_1158_ = stack[3].m_obj;
lean_object* v_a_1159_ = stack[4].m_obj;
lean_object* v_a_1160_ = stack[5].m_obj;
lean_object* v_res_1164_;
v_res_1164_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
stack->m_obj
 = v_res_1164_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___boxed(lean_object* v_e_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1173_, lean_object* v_m_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_1174_, v_a_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1177_, lean_object* v_m_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(v_00_u03b2_1177_, v_m_1178_, v_a_1179_);
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_m_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1181_, lean_object* v_m_1182_, lean_object* v_a_1183_, lean_object* v_b_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v_m_1182_, v_a_1183_, v_b_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1186_, lean_object* v_a_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_1187_, v_x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1190_, lean_object* v_a_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_1190_, v_a_1191_, v_x_1192_);
lean_dec(v_x_1192_);
lean_dec_ref(v_a_1191_);
return v_res_1193_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1194_, lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_1195_, v_x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1195_ = stack[1].m_obj;
lean_object* v_x_1196_ = stack[2].m_obj;
uint8_t v_res_1198_;
v_res_1198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_a_1195_, v_x_1196_);
stack->m_num = v_res_1198_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1199_, lean_object* v_a_1200_, lean_object* v_x_1201_){
_start:
{
uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1199_, v_a_1200_, v_x_1201_);
lean_dec(v_x_1201_);
lean_dec_ref(v_a_1200_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1204_, lean_object* v_data_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_data_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1207_, lean_object* v_a_1208_, lean_object* v_b_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_1208_, v_b_1209_, v_x_1210_);
return v___x_1211_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_1212_, lean_object* v_name_1213_, uint8_t v_bi_1214_, lean_object* v_type_1215_, lean_object* v_k_1216_, uint8_t v_kind_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_1213_, v_bi_1214_, v_type_1215_, v_k_1216_, v_kind_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1213_ = stack[1].m_obj;
uint8_t v_bi_1214_ = stack[2].m_num;
lean_object* v_type_1215_ = stack[3].m_obj;
lean_object* v_k_1216_ = stack[4].m_obj;
uint8_t v_kind_1217_ = stack[5].m_num;
lean_object* v___y_1218_ = stack[6].m_obj;
lean_object* v___y_1219_ = stack[7].m_obj;
lean_object* v___y_1220_ = stack[8].m_obj;
lean_object* v___y_1221_ = stack[9].m_obj;
lean_object* v___y_1222_ = stack[10].m_obj;
lean_object* v___y_1223_ = stack[11].m_obj;
lean_object* v_res_1226_;
v_res_1226_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(lean_box(0), v_name_1213_, v_bi_1214_, v_type_1215_, v_k_1216_, v_kind_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
stack->m_obj
 = v_res_1226_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_name_1228_, lean_object* v_bi_1229_, lean_object* v_type_1230_, lean_object* v_k_1231_, lean_object* v_kind_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_bi_boxed_1240_; uint8_t v_kind_boxed_1241_; lean_object* v_res_1242_; 
v_bi_boxed_1240_ = lean_unbox(v_bi_1229_);
v_kind_boxed_1241_ = lean_unbox(v_kind_1232_);
v_res_1242_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_1227_, v_name_1228_, v_bi_boxed_1240_, v_type_1230_, v_k_1231_, v_kind_boxed_1241_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec(v___y_1233_);
return v_res_1242_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(lean_object* v_00_u03b1_1243_, lean_object* v_name_1244_, lean_object* v_type_1245_, lean_object* v_val_1246_, lean_object* v_k_1247_, uint8_t v_nondep_1248_, uint8_t v_kind_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_1244_, v_type_1245_, v_val_1246_, v_k_1247_, v_nondep_1248_, v_kind_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1244_ = stack[1].m_obj;
lean_object* v_type_1245_ = stack[2].m_obj;
lean_object* v_val_1246_ = stack[3].m_obj;
lean_object* v_k_1247_ = stack[4].m_obj;
uint8_t v_nondep_1248_ = stack[5].m_num;
uint8_t v_kind_1249_ = stack[6].m_num;
lean_object* v___y_1250_ = stack[7].m_obj;
lean_object* v___y_1251_ = stack[8].m_obj;
lean_object* v___y_1252_ = stack[9].m_obj;
lean_object* v___y_1253_ = stack[10].m_obj;
lean_object* v___y_1254_ = stack[11].m_obj;
lean_object* v___y_1255_ = stack[12].m_obj;
lean_object* v_res_1258_;
v_res_1258_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(lean_box(0), v_name_1244_, v_type_1245_, v_val_1246_, v_k_1247_, v_nondep_1248_, v_kind_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
stack->m_obj
 = v_res_1258_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1259_, lean_object* v_name_1260_, lean_object* v_type_1261_, lean_object* v_val_1262_, lean_object* v_k_1263_, lean_object* v_nondep_1264_, lean_object* v_kind_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
uint8_t v_nondep_boxed_1273_; uint8_t v_kind_boxed_1274_; lean_object* v_res_1275_; 
v_nondep_boxed_1273_ = lean_unbox(v_nondep_1264_);
v_kind_boxed_1274_ = lean_unbox(v_kind_1265_);
v_res_1275_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(v_00_u03b1_1259_, v_name_1260_, v_type_1261_, v_val_1262_, v_k_1263_, v_nondep_boxed_1273_, v_kind_boxed_1274_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_1276_, lean_object* v_i_1277_, lean_object* v_source_1278_, lean_object* v_target_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_i_1277_, v_source_1278_, v_target_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10(lean_object* v_00_u03b2_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_x_1282_, v_x_1283_);
return v___x_1284_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(lean_object* v_k_1285_, lean_object* v___y_1286_, lean_object* v_b_1287_, lean_object* v_c_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
lean_inc(v___y_1286_);
v___x_1294_ = lean_apply_8(v_k_1285_, v_b_1287_, v_c_1288_, v___y_1286_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, lean_box(0));
return v___x_1294_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1285_ = stack[0].m_obj;
lean_object* v___y_1286_ = stack[1].m_obj;
lean_object* v_b_1287_ = stack[2].m_obj;
lean_object* v_c_1288_ = stack[3].m_obj;
lean_object* v___y_1289_ = stack[4].m_obj;
lean_object* v___y_1290_ = stack[5].m_obj;
lean_object* v___y_1291_ = stack[6].m_obj;
lean_object* v___y_1292_ = stack[7].m_obj;
lean_object* v_res_1295_;
v_res_1295_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(v_k_1285_, v___y_1286_, v_b_1287_, v_c_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
stack->m_obj
 = v_res_1295_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_1296_, lean_object* v___y_1297_, lean_object* v_b_1298_, lean_object* v_c_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(v_k_1296_, v___y_1297_, v_b_1298_, v_c_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1297_);
return v_res_1305_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(lean_object* v_type_1306_, lean_object* v_maxFVars_x3f_1307_, lean_object* v_k_1308_, uint8_t v_cleanupAnnotations_1309_, uint8_t v_whnfType_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___f_1317_; lean_object* v___x_1318_; 
lean_inc(v___y_1311_);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1317_, 0, v_k_1308_);
lean_closure_set(v___f_1317_, 1, v___y_1311_);
v___x_1318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1306_, v_maxFVars_x3f_1307_, v___f_1317_, v_cleanupAnnotations_1309_, v_whnfType_1310_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
return v___x_1318_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1306_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_1307_ = stack[1].m_obj;
lean_object* v_k_1308_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1309_ = stack[3].m_num;
uint8_t v_whnfType_1310_ = stack[4].m_num;
lean_object* v___y_1311_ = stack[5].m_obj;
lean_object* v___y_1312_ = stack[6].m_obj;
lean_object* v___y_1313_ = stack[7].m_obj;
lean_object* v___y_1314_ = stack[8].m_obj;
lean_object* v___y_1315_ = stack[9].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_1306_, v_maxFVars_x3f_1307_, v_k_1308_, v_cleanupAnnotations_1309_, v_whnfType_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___boxed(lean_object* v_type_1328_, lean_object* v_maxFVars_x3f_1329_, lean_object* v_k_1330_, lean_object* v_cleanupAnnotations_1331_, lean_object* v_whnfType_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1339_; uint8_t v_whnfType_boxed_1340_; lean_object* v_res_1341_; 
v_cleanupAnnotations_boxed_1339_ = lean_unbox(v_cleanupAnnotations_1331_);
v_whnfType_boxed_1340_ = lean_unbox(v_whnfType_1332_);
v_res_1341_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_1328_, v_maxFVars_x3f_1329_, v_k_1330_, v_cleanupAnnotations_boxed_1339_, v_whnfType_boxed_1340_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
return v_res_1341_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(lean_object* v_00_u03b1_1342_, lean_object* v_type_1343_, lean_object* v_maxFVars_x3f_1344_, lean_object* v_k_1345_, uint8_t v_cleanupAnnotations_1346_, uint8_t v_whnfType_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_1343_, v_maxFVars_x3f_1344_, v_k_1345_, v_cleanupAnnotations_1346_, v_whnfType_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1343_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_1344_ = stack[2].m_obj;
lean_object* v_k_1345_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_1346_ = stack[4].m_num;
uint8_t v_whnfType_1347_ = stack[5].m_num;
lean_object* v___y_1348_ = stack[6].m_obj;
lean_object* v___y_1349_ = stack[7].m_obj;
lean_object* v___y_1350_ = stack[8].m_obj;
lean_object* v___y_1351_ = stack[9].m_obj;
lean_object* v___y_1352_ = stack[10].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(lean_box(0), v_type_1343_, v_maxFVars_x3f_1344_, v_k_1345_, v_cleanupAnnotations_1346_, v_whnfType_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_type_1357_, lean_object* v_maxFVars_x3f_1358_, lean_object* v_k_1359_, lean_object* v_cleanupAnnotations_1360_, lean_object* v_whnfType_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1368_; uint8_t v_whnfType_boxed_1369_; lean_object* v_res_1370_; 
v_cleanupAnnotations_boxed_1368_ = lean_unbox(v_cleanupAnnotations_1360_);
v_whnfType_boxed_1369_ = lean_unbox(v_whnfType_1361_);
v_res_1370_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(v_00_u03b1_1356_, v_type_1357_, v_maxFVars_x3f_1358_, v_k_1359_, v_cleanupAnnotations_boxed_1368_, v_whnfType_boxed_1369_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed(lean_object* v___x_1371_, lean_object* v_currentBinderIdx_1372_, lean_object* v___x_1373_, lean_object* v_currentFVars_1374_, lean_object* v_p_1375_, lean_object* v_fvar_1376_, lean_object* v_e_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(v___x_1371_, v_currentBinderIdx_1372_, v___x_1373_, v_currentFVars_1374_, v_p_1375_, v_fvar_1376_, v_e_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v_fvar_1376_);
lean_dec(v___x_1373_);
lean_dec_ref(v___x_1371_);
return v_res_1384_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(lean_object* v_p_1387_, lean_object* v_e_1388_, lean_object* v_currentBinderIdx_1389_, lean_object* v_currentFVars_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_e_1397_; uint8_t v___x_1398_; 
v_e_1397_ = l_Lean_Expr_cleanupAnnotations(v_e_1388_);
v___x_1398_ = l_Lean_Expr_isForall(v_e_1397_);
if (v___x_1398_ == 0)
{
if (lean_obj_tag(v_e_1397_) == 8)
{
lean_object* v_type_1399_; lean_object* v_body_1400_; lean_object* v___x_1401_; 
v_type_1399_ = lean_ctor_get(v_e_1397_, 1);
lean_inc_ref_n(v_type_1399_, 2);
v_body_1400_ = lean_ctor_get(v_e_1397_, 3);
lean_inc_ref(v_body_1400_);
lean_dec_ref_known(v_e_1397_, 4);
v___x_1401_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_type_1399_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1402_; 
lean_dec_ref_known(v___x_1401_, 1);
v___x_1402_ = l_Lean_Meta_mkSorry(v_type_1399_, v___x_1398_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1404_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = lean_expr_instantiate1(v_body_1400_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_body_1400_);
v_e_1388_ = v___x_1404_;
goto _start;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v_body_1400_);
lean_dec_ref(v_currentFVars_1390_);
lean_dec(v_currentBinderIdx_1389_);
lean_dec_ref(v_p_1387_);
v_a_1406_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1402_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1402_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_body_1400_);
lean_dec_ref(v_type_1399_);
lean_dec_ref(v_currentFVars_1390_);
lean_dec(v_currentBinderIdx_1389_);
lean_dec_ref(v_p_1387_);
v_a_1414_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1401_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1401_);
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
lean_object* v___x_1422_; 
lean_dec(v_currentBinderIdx_1389_);
lean_dec_ref(v_p_1387_);
v___x_1422_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_1397_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1422_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v___x_1422_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_currentFVars_1390_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_currentFVars_1390_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_currentFVars_1390_);
v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1422_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1422_);
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
else
{
lean_object* v_binderType_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_binderType_1439_ = lean_ctor_get(v_e_1397_, 1);
v___x_1440_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_binderType_1439_);
v___x_1441_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_binderType_1439_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1441_) == 0)
{
uint8_t v___y_1443_; uint8_t v___x_1464_; uint8_t v___x_1465_; 
lean_dec_ref_known(v___x_1441_, 1);
v___x_1464_ = l_Lean_Expr_binderInfo(v_e_1397_);
v___x_1465_ = l_Lean_BinderInfo_isInstImplicit(v___x_1464_);
if (v___x_1465_ == 0)
{
v___y_1443_ = v___x_1465_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
lean_inc_ref(v_p_1387_);
lean_inc_ref(v_binderType_1439_);
v___x_1466_ = lean_apply_1(v_p_1387_, v_binderType_1439_);
v___x_1467_ = lean_unbox(v___x_1466_);
v___y_1443_ = v___x_1467_;
goto v___jp_1442_;
}
v___jp_1442_:
{
if (v___y_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_inc_ref(v_binderType_1439_);
v___x_1444_ = l_Lean_Meta_mkSorry(v_binderType_1439_, v___y_1443_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_body_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v_body_1446_ = lean_ctor_get(v_e_1397_, 2);
lean_inc_ref(v_body_1446_);
lean_dec_ref(v_e_1397_);
v___x_1447_ = lean_expr_instantiate1(v_body_1446_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref(v_body_1446_);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_currentBinderIdx_1389_, v___x_1448_);
lean_dec(v_currentBinderIdx_1389_);
v_e_1388_ = v___x_1447_;
v_currentBinderIdx_1389_ = v___x_1449_;
goto _start;
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_currentFVars_1390_);
lean_dec(v_currentBinderIdx_1389_);
lean_dec_ref(v_p_1387_);
v_a_1451_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1444_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1444_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v___x_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1459_ = lean_unsigned_to_nat(1u);
v___f_1460_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1460_, 0, v___x_1440_);
lean_closure_set(v___f_1460_, 1, v_currentBinderIdx_1389_);
lean_closure_set(v___f_1460_, 2, v___x_1459_);
lean_closure_set(v___f_1460_, 3, v_currentFVars_1390_);
lean_closure_set(v___f_1460_, 4, v_p_1387_);
v___x_1461_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0));
v___x_1462_ = 0;
v___x_1463_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_e_1397_, v___x_1461_, v___f_1460_, v___x_1462_, v___x_1462_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1463_;
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_currentFVars_1390_);
lean_dec(v_currentBinderIdx_1389_);
lean_dec_ref(v_p_1387_);
v_a_1468_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1441_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1441_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1387_ = stack[0].m_obj;
lean_object* v_e_1388_ = stack[1].m_obj;
lean_object* v_currentBinderIdx_1389_ = stack[2].m_obj;
lean_object* v_currentFVars_1390_ = stack[3].m_obj;
lean_object* v_a_1391_ = stack[4].m_obj;
lean_object* v_a_1392_ = stack[5].m_obj;
lean_object* v_a_1393_ = stack[6].m_obj;
lean_object* v_a_1394_ = stack[7].m_obj;
lean_object* v_a_1395_ = stack[8].m_obj;
lean_object* v_res_1476_;
v_res_1476_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1387_, v_e_1388_, v_currentBinderIdx_1389_, v_currentFVars_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
stack->m_obj
 = v_res_1476_;
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(lean_object* v___x_1477_, lean_object* v_currentBinderIdx_1478_, lean_object* v___x_1479_, lean_object* v_currentFVars_1480_, lean_object* v_p_1481_, lean_object* v_fvar_1482_, lean_object* v_e_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_array_get_borrowed(v___x_1477_, v_fvar_1482_, v___x_1490_);
v___x_1492_ = l_Lean_Expr_fvarId_x21(v___x_1491_);
v___x_1493_ = lean_nat_add(v_currentBinderIdx_1478_, v___x_1479_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v_currentBinderIdx_1478_);
v___x_1495_ = lean_array_push(v_currentFVars_1480_, v___x_1494_);
v___x_1496_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1481_, v_e_1483_, v___x_1493_, v___x_1495_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1496_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1477_ = stack[0].m_obj;
lean_object* v_currentBinderIdx_1478_ = stack[1].m_obj;
lean_object* v___x_1479_ = stack[2].m_obj;
lean_object* v_currentFVars_1480_ = stack[3].m_obj;
lean_object* v_p_1481_ = stack[4].m_obj;
lean_object* v_fvar_1482_ = stack[5].m_obj;
lean_object* v_e_1483_ = stack[6].m_obj;
lean_object* v___y_1484_ = stack[7].m_obj;
lean_object* v___y_1485_ = stack[8].m_obj;
lean_object* v___y_1486_ = stack[9].m_obj;
lean_object* v___y_1487_ = stack[10].m_obj;
lean_object* v___y_1488_ = stack[11].m_obj;
lean_object* v_res_1497_;
v_res_1497_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(v___x_1477_, v_currentBinderIdx_1478_, v___x_1479_, v_currentFVars_1480_, v_p_1481_, v_fvar_1482_, v_e_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
stack->m_obj
 = v_res_1497_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___boxed(lean_object* v_p_1498_, lean_object* v_e_1499_, lean_object* v_currentBinderIdx_1500_, lean_object* v_currentFVars_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1498_, v_e_1499_, v_currentBinderIdx_1500_, v_currentFVars_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
return v_res_1508_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(lean_object* v_k_1509_, lean_object* v_t_1510_){
_start:
{
if (lean_obj_tag(v_t_1510_) == 0)
{
lean_object* v_k_1511_; lean_object* v_l_1512_; lean_object* v_r_1513_; uint8_t v___x_1514_; 
v_k_1511_ = lean_ctor_get(v_t_1510_, 1);
v_l_1512_ = lean_ctor_get(v_t_1510_, 3);
v_r_1513_ = lean_ctor_get(v_t_1510_, 4);
v___x_1514_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1509_, v_k_1511_);
switch(v___x_1514_)
{
case 0:
{
v_t_1510_ = v_l_1512_;
goto _start;
}
case 1:
{
uint8_t v___x_1516_; 
v___x_1516_ = 1;
return v___x_1516_;
}
default: 
{
v_t_1510_ = v_r_1513_;
goto _start;
}
}
}
else
{
uint8_t v___x_1518_; 
v___x_1518_ = 0;
return v___x_1518_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1509_ = stack[0].m_obj;
lean_object* v_t_1510_ = stack[1].m_obj;
uint8_t v_res_1519_;
v_res_1519_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_1509_, v_t_1510_);
stack->m_num = v_res_1519_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg___boxed(lean_object* v_k_1520_, lean_object* v_t_1521_){
_start:
{
uint8_t v_res_1522_; lean_object* v_r_1523_; 
v_res_1522_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_1520_, v_t_1521_);
lean_dec(v_t_1521_);
lean_dec(v_k_1520_);
v_r_1523_ = lean_box(v_res_1522_);
return v_r_1523_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(lean_object* v_val_1524_, lean_object* v_as_1525_, size_t v_i_1526_, size_t v_stop_1527_, lean_object* v_b_1528_){
_start:
{
lean_object* v___y_1530_; uint8_t v___x_1534_; 
v___x_1534_ = lean_usize_dec_eq(v_i_1526_, v_stop_1527_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v_fvarId_1536_; lean_object* v_idx_1537_; uint8_t v___x_1538_; 
v___x_1535_ = lean_array_uget_borrowed(v_as_1525_, v_i_1526_);
v_fvarId_1536_ = lean_ctor_get(v___x_1535_, 0);
v_idx_1537_ = lean_ctor_get(v___x_1535_, 1);
v___x_1538_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_fvarId_1536_, v_val_1524_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
lean_inc(v_idx_1537_);
v___x_1539_ = lean_array_push(v_b_1528_, v_idx_1537_);
v___y_1530_ = v___x_1539_;
goto v___jp_1529_;
}
else
{
v___y_1530_ = v_b_1528_;
goto v___jp_1529_;
}
}
else
{
return v_b_1528_;
}
v___jp_1529_:
{
size_t v___x_1531_; size_t v___x_1532_; 
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_add(v_i_1526_, v___x_1531_);
v_i_1526_ = v___x_1532_;
v_b_1528_ = v___y_1530_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1524_ = stack[0].m_obj;
lean_object* v_as_1525_ = stack[1].m_obj;
size_t v_i_1526_ = stack[2].m_num;
size_t v_stop_1527_ = stack[3].m_num;
lean_object* v_b_1528_ = stack[4].m_obj;
lean_object* v_res_1540_;
v_res_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1524_, v_as_1525_, v_i_1526_, v_stop_1527_, v_b_1528_);
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1___boxed(lean_object* v_val_1541_, lean_object* v_as_1542_, lean_object* v_i_1543_, lean_object* v_stop_1544_, lean_object* v_b_1545_){
_start:
{
size_t v_i_boxed_1546_; size_t v_stop_boxed_1547_; lean_object* v_res_1548_; 
v_i_boxed_1546_ = lean_unbox_usize(v_i_1543_);
lean_dec(v_i_1543_);
v_stop_boxed_1547_ = lean_unbox_usize(v_stop_1544_);
lean_dec(v_stop_1544_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1541_, v_as_1542_, v_i_boxed_1546_, v_stop_boxed_1547_, v_b_1545_);
lean_dec_ref(v_as_1542_);
lean_dec(v_val_1541_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(lean_object* v_val_1549_, lean_object* v_as_1550_, lean_object* v_start_1551_, lean_object* v_stop_1552_){
_start:
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1553_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0));
v___x_1554_ = lean_nat_dec_lt(v_start_1551_, v_stop_1552_);
if (v___x_1554_ == 0)
{
return v___x_1553_;
}
else
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = lean_array_get_size(v_as_1550_);
v___x_1556_ = lean_nat_dec_le(v_stop_1552_, v___x_1555_);
if (v___x_1556_ == 0)
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_lt(v_start_1551_, v___x_1555_);
if (v___x_1557_ == 0)
{
return v___x_1553_;
}
else
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_usize_of_nat(v_start_1551_);
v___x_1559_ = lean_usize_of_nat(v___x_1555_);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1549_, v_as_1550_, v___x_1558_, v___x_1559_, v___x_1553_);
return v___x_1560_;
}
}
else
{
size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_usize_of_nat(v_start_1551_);
v___x_1562_ = lean_usize_of_nat(v_stop_1552_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_1549_, v_as_1550_, v___x_1561_, v___x_1562_, v___x_1553_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1___boxed(lean_object* v_val_1564_, lean_object* v_as_1565_, lean_object* v_start_1566_, lean_object* v_stop_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v_val_1564_, v_as_1565_, v_start_1566_, v_stop_1567_);
lean_dec(v_stop_1567_);
lean_dec(v_start_1566_);
lean_dec_ref(v_as_1565_);
lean_dec(v_val_1564_);
return v_res_1568_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(lean_object* v_p_1571_, lean_object* v_e_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1578_ = lean_box(1);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0));
v___x_1581_ = lean_st_mk_ref(v___x_1578_);
v___x_1582_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_1571_, v_e_1572_, v___x_1579_, v___x_1580_, v___x_1581_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1593_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1587_ = lean_st_ref_get(v___x_1581_);
lean_dec(v___x_1581_);
v___x_1588_ = lean_array_get_size(v_a_1583_);
v___x_1589_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v___x_1587_, v_a_1583_, v___x_1579_, v___x_1588_);
lean_dec(v_a_1583_);
lean_dec(v___x_1587_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1589_);
v___x_1591_ = v___x_1585_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v___x_1581_);
v_a_1594_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1582_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1582_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1571_ = stack[0].m_obj;
lean_object* v_e_1572_ = stack[1].m_obj;
lean_object* v_a_1573_ = stack[2].m_obj;
lean_object* v_a_1574_ = stack[3].m_obj;
lean_object* v_a_1575_ = stack[4].m_obj;
lean_object* v_a_1576_ = stack[5].m_obj;
lean_object* v_res_1602_;
v_res_1602_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_1571_, v_e_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
stack->m_obj
 = v_res_1602_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___boxed(lean_object* v_p_1603_, lean_object* v_e_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_1603_, v_e_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
return v_res_1610_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(lean_object* v_00_u03b2_1611_, lean_object* v_k_1612_, lean_object* v_t_1613_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_1612_, v_t_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1612_ = stack[1].m_obj;
lean_object* v_t_1613_ = stack[2].m_obj;
uint8_t v_res_1615_;
v_res_1615_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(lean_box(0), v_k_1612_, v_t_1613_);
stack->m_num = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_k_1617_, lean_object* v_t_1618_){
_start:
{
uint8_t v_res_1619_; lean_object* v_r_1620_; 
v_res_1619_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(v_00_u03b2_1616_, v_k_1617_, v_t_1618_);
lean_dec(v_t_1618_);
lean_dec(v_k_1617_);
v_r_1620_ = lean_box(v_res_1619_);
return v_r_1620_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(lean_object* v_k_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v_b_1624_, lean_object* v_c_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc_ref(v___y_1626_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1631_ = lean_apply_9(v_k_1621_, v_b_1624_, v_c_1625_, v___y_1622_, v___y_1623_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, lean_box(0));
return v___x_1631_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1621_ = stack[0].m_obj;
lean_object* v___y_1622_ = stack[1].m_obj;
lean_object* v___y_1623_ = stack[2].m_obj;
lean_object* v_b_1624_ = stack[3].m_obj;
lean_object* v_c_1625_ = stack[4].m_obj;
lean_object* v___y_1626_ = stack[5].m_obj;
lean_object* v___y_1627_ = stack[6].m_obj;
lean_object* v___y_1628_ = stack[7].m_obj;
lean_object* v___y_1629_ = stack[8].m_obj;
lean_object* v_res_1632_;
v_res_1632_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(v_k_1621_, v___y_1622_, v___y_1623_, v_b_1624_, v_c_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
stack->m_obj
 = v_res_1632_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed(lean_object* v_k_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v_b_1636_, lean_object* v_c_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(v_k_1633_, v___y_1634_, v___y_1635_, v_b_1636_, v_c_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1643_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(lean_object* v_type_1644_, lean_object* v_maxFVars_x3f_1645_, lean_object* v_k_1646_, uint8_t v_cleanupAnnotations_1647_, uint8_t v_whnfType_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___f_1656_; lean_object* v___x_1657_; 
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
v___f_1656_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1656_, 0, v_k_1646_);
lean_closure_set(v___f_1656_, 1, v___y_1649_);
lean_closure_set(v___f_1656_, 2, v___y_1650_);
v___x_1657_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1644_, v_maxFVars_x3f_1645_, v___f_1656_, v_cleanupAnnotations_1647_, v_whnfType_1648_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
if (lean_obj_tag(v___x_1657_) == 0)
{
return v___x_1657_;
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1644_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_1645_ = stack[1].m_obj;
lean_object* v_k_1646_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1647_ = stack[3].m_num;
uint8_t v_whnfType_1648_ = stack[4].m_num;
lean_object* v___y_1649_ = stack[5].m_obj;
lean_object* v___y_1650_ = stack[6].m_obj;
lean_object* v___y_1651_ = stack[7].m_obj;
lean_object* v___y_1652_ = stack[8].m_obj;
lean_object* v___y_1653_ = stack[9].m_obj;
lean_object* v___y_1654_ = stack[10].m_obj;
lean_object* v_res_1666_;
v_res_1666_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1644_, v_maxFVars_x3f_1645_, v_k_1646_, v_cleanupAnnotations_1647_, v_whnfType_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
stack->m_obj
 = v_res_1666_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___boxed(lean_object* v_type_1667_, lean_object* v_maxFVars_x3f_1668_, lean_object* v_k_1669_, lean_object* v_cleanupAnnotations_1670_, lean_object* v_whnfType_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1679_; uint8_t v_whnfType_boxed_1680_; lean_object* v_res_1681_; 
v_cleanupAnnotations_boxed_1679_ = lean_unbox(v_cleanupAnnotations_1670_);
v_whnfType_boxed_1680_ = lean_unbox(v_whnfType_1671_);
v_res_1681_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1667_, v_maxFVars_x3f_1668_, v_k_1669_, v_cleanupAnnotations_boxed_1679_, v_whnfType_boxed_1680_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1681_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(lean_object* v_00_u03b1_1682_, lean_object* v_type_1683_, lean_object* v_maxFVars_x3f_1684_, lean_object* v_k_1685_, uint8_t v_cleanupAnnotations_1686_, uint8_t v_whnfType_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1683_, v_maxFVars_x3f_1684_, v_k_1685_, v_cleanupAnnotations_1686_, v_whnfType_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1683_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_1684_ = stack[2].m_obj;
lean_object* v_k_1685_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_1686_ = stack[4].m_num;
uint8_t v_whnfType_1687_ = stack[5].m_num;
lean_object* v___y_1688_ = stack[6].m_obj;
lean_object* v___y_1689_ = stack[7].m_obj;
lean_object* v___y_1690_ = stack[8].m_obj;
lean_object* v___y_1691_ = stack[9].m_obj;
lean_object* v___y_1692_ = stack[10].m_obj;
lean_object* v___y_1693_ = stack[11].m_obj;
lean_object* v_res_1696_;
v_res_1696_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(lean_box(0), v_type_1683_, v_maxFVars_x3f_1684_, v_k_1685_, v_cleanupAnnotations_1686_, v_whnfType_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
stack->m_obj
 = v_res_1696_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___boxed(lean_object* v_00_u03b1_1697_, lean_object* v_type_1698_, lean_object* v_maxFVars_x3f_1699_, lean_object* v_k_1700_, lean_object* v_cleanupAnnotations_1701_, lean_object* v_whnfType_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1710_; uint8_t v_whnfType_boxed_1711_; lean_object* v_res_1712_; 
v_cleanupAnnotations_boxed_1710_ = lean_unbox(v_cleanupAnnotations_1701_);
v_whnfType_boxed_1711_ = lean_unbox(v_whnfType_1702_);
v_res_1712_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(v_00_u03b1_1697_, v_type_1698_, v_maxFVars_x3f_1699_, v_k_1700_, v_cleanupAnnotations_boxed_1710_, v_whnfType_boxed_1711_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
return v_res_1712_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(lean_object* v_a_1713_, lean_object* v_as_1714_, size_t v_i_1715_, size_t v_stop_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_usize_dec_eq(v_i_1715_, v_stop_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = lean_array_uget_borrowed(v_as_1714_, v_i_1715_);
v___x_1719_ = lean_nat_dec_eq(v_a_1713_, v___x_1718_);
if (v___x_1719_ == 0)
{
size_t v___x_1720_; size_t v___x_1721_; 
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1715_, v___x_1720_);
v_i_1715_ = v___x_1721_;
goto _start;
}
else
{
return v___x_1719_;
}
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1713_ = stack[0].m_obj;
lean_object* v_as_1714_ = stack[1].m_obj;
size_t v_i_1715_ = stack[2].m_num;
size_t v_stop_1716_ = stack[3].m_num;
uint8_t v_res_1724_;
v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_1713_, v_as_1714_, v_i_1715_, v_stop_1716_);
stack->m_num = v_res_1724_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0___boxed(lean_object* v_a_1725_, lean_object* v_as_1726_, lean_object* v_i_1727_, lean_object* v_stop_1728_){
_start:
{
size_t v_i_boxed_1729_; size_t v_stop_boxed_1730_; uint8_t v_res_1731_; lean_object* v_r_1732_; 
v_i_boxed_1729_ = lean_unbox_usize(v_i_1727_);
lean_dec(v_i_1727_);
v_stop_boxed_1730_ = lean_unbox_usize(v_stop_1728_);
lean_dec(v_stop_1728_);
v_res_1731_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_1725_, v_as_1726_, v_i_boxed_1729_, v_stop_boxed_1730_);
lean_dec_ref(v_as_1726_);
lean_dec(v_a_1725_);
v_r_1732_ = lean_box(v_res_1731_);
return v_r_1732_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(lean_object* v_as_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_array_get_size(v_as_1733_);
v___x_1737_ = lean_nat_dec_lt(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
return v___x_1737_;
}
else
{
if (v___x_1737_ == 0)
{
return v___x_1737_;
}
else
{
size_t v___x_1738_; size_t v___x_1739_; uint8_t v___x_1740_; 
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = lean_usize_of_nat(v___x_1736_);
v___x_1740_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_1734_, v_as_1733_, v___x_1738_, v___x_1739_);
return v___x_1740_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1733_ = stack[0].m_obj;
lean_object* v_a_1734_ = stack[1].m_obj;
uint8_t v_res_1741_;
v_res_1741_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v_as_1733_, v_a_1734_);
stack->m_num = v_res_1741_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0___boxed(lean_object* v_as_1742_, lean_object* v_a_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v_as_1742_, v_a_1743_);
lean_dec(v_a_1743_);
lean_dec_ref(v_as_1742_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v___x_1748_, uint8_t v___x_1749_, lean_object* v_fvars_1750_, size_t v_sz_1751_, size_t v_i_1752_, lean_object* v_bs_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_usize_dec_lt(v_i_1752_, v_sz_1751_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_bs_1753_);
return v___x_1760_;
}
else
{
uint8_t v___x_1761_; lean_object* v_v_1762_; lean_object* v___x_1763_; lean_object* v_bs_x27_1764_; lean_object* v___y_1766_; lean_object* v___y_1767_; uint8_t v___y_1768_; lean_object* v___y_1775_; lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1761_ = lean_nat_dec_lt(v___x_1747_, v___x_1748_);
v_v_1762_ = lean_array_uget(v_bs_1753_, v_i_1752_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v_bs_x27_1764_ = lean_array_uset(v_bs_1753_, v_i_1752_, v___x_1763_);
v___x_1778_ = lean_array_get_size(v_fvars_1750_);
v___x_1779_ = lean_nat_dec_lt(v_v_1762_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_box(0);
v___y_1775_ = v___x_1780_;
v_a_1776_ = v___x_1780_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_array_fget_borrowed(v_fvars_1750_, v_v_1762_);
lean_inc_n(v___x_1781_, 2);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_inc(v___y_1757_);
lean_inc_ref(v___y_1756_);
lean_inc(v___y_1755_);
lean_inc_ref(v___y_1754_);
v___x_1783_ = lean_infer_type(v___x_1781_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_a_1784_);
v___y_1775_ = v___x_1782_;
v_a_1776_ = v___x_1785_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref_known(v___x_1782_, 1);
lean_dec_ref(v_bs_x27_1764_);
lean_dec(v_v_1762_);
v_a_1786_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1783_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
v___jp_1765_:
{
lean_object* v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1769_, 0, v___y_1767_);
lean_ctor_set(v___x_1769_, 1, v___y_1766_);
lean_ctor_set(v___x_1769_, 2, v_v_1762_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*3, v___y_1768_);
v___x_1770_ = ((size_t)1ULL);
v___x_1771_ = lean_usize_add(v_i_1752_, v___x_1770_);
v___x_1772_ = lean_array_uset(v_bs_x27_1764_, v_i_1752_, v___x_1769_);
v_i_1752_ = v___x_1771_;
v_bs_1753_ = v___x_1772_;
goto _start;
}
v___jp_1774_:
{
uint8_t v___x_1777_; 
v___x_1777_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v___x_1746_, v_v_1762_);
if (v___x_1777_ == 0)
{
v___y_1766_ = v_a_1776_;
v___y_1767_ = v___y_1775_;
v___y_1768_ = v___x_1761_;
goto v___jp_1765_;
}
else
{
v___y_1766_ = v_a_1776_;
v___y_1767_ = v___y_1775_;
v___y_1768_ = v___x_1749_;
goto v___jp_1765_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1746_ = stack[0].m_obj;
lean_object* v___x_1747_ = stack[1].m_obj;
lean_object* v___x_1748_ = stack[2].m_obj;
uint8_t v___x_1749_ = stack[3].m_num;
lean_object* v_fvars_1750_ = stack[4].m_obj;
size_t v_sz_1751_ = stack[5].m_num;
size_t v_i_1752_ = stack[6].m_num;
lean_object* v_bs_1753_ = stack[7].m_obj;
lean_object* v___y_1754_ = stack[8].m_obj;
lean_object* v___y_1755_ = stack[9].m_obj;
lean_object* v___y_1756_ = stack[10].m_obj;
lean_object* v___y_1757_ = stack[11].m_obj;
lean_object* v_res_1794_;
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1746_, v___x_1747_, v___x_1748_, v___x_1749_, v_fvars_1750_, v_sz_1751_, v_i_1752_, v_bs_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
stack->m_obj
 = v_res_1794_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg___boxed(lean_object* v___x_1795_, lean_object* v___x_1796_, lean_object* v___x_1797_, lean_object* v___x_1798_, lean_object* v_fvars_1799_, lean_object* v_sz_1800_, lean_object* v_i_1801_, lean_object* v_bs_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v___x_3349__boxed_1808_; size_t v_sz_boxed_1809_; size_t v_i_boxed_1810_; lean_object* v_res_1811_; 
v___x_3349__boxed_1808_ = lean_unbox(v___x_1798_);
v_sz_boxed_1809_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1810_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1795_, v___x_1796_, v___x_1797_, v___x_3349__boxed_1808_, v_fvars_1799_, v_sz_boxed_1809_, v_i_boxed_1810_, v_bs_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_fvars_1799_);
lean_dec(v___x_1797_);
lean_dec(v___x_1796_);
lean_dec_ref(v___x_1795_);
return v_res_1811_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(lean_object* v_p_1812_, lean_object* v_type_1813_, lean_object* v_a_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, uint8_t v___x_1817_, lean_object* v_logOnUnused_1818_, lean_object* v_fvars_1819_, lean_object* v_x_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; size_t v_sz_1829_; size_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(v_p_1812_, v_type_1813_);
v_sz_1829_ = lean_array_size(v_a_1814_);
v___x_1830_ = ((size_t)0ULL);
v___x_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1828_, v___x_1815_, v___x_1816_, v___x_1817_, v_fvars_1819_, v_sz_1829_, v___x_1830_, v_a_1814_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec_ref(v___x_1828_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
lean_inc(v___y_1822_);
lean_inc_ref(v___y_1821_);
v___x_1833_ = lean_apply_8(v_logOnUnused_1818_, v_a_1832_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, lean_box(0));
return v___x_1833_;
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_logOnUnused_1818_);
v_a_1834_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1831_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1831_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1812_ = stack[0].m_obj;
lean_object* v_type_1813_ = stack[1].m_obj;
lean_object* v_a_1814_ = stack[2].m_obj;
lean_object* v___x_1815_ = stack[3].m_obj;
lean_object* v___x_1816_ = stack[4].m_obj;
uint8_t v___x_1817_ = stack[5].m_num;
lean_object* v_logOnUnused_1818_ = stack[6].m_obj;
lean_object* v_fvars_1819_ = stack[7].m_obj;
lean_object* v_x_1820_ = stack[8].m_obj;
lean_object* v___y_1821_ = stack[9].m_obj;
lean_object* v___y_1822_ = stack[10].m_obj;
lean_object* v___y_1823_ = stack[11].m_obj;
lean_object* v___y_1824_ = stack[12].m_obj;
lean_object* v___y_1825_ = stack[13].m_obj;
lean_object* v___y_1826_ = stack[14].m_obj;
lean_object* v_res_1842_;
v_res_1842_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(v_p_1812_, v_type_1813_, v_a_1814_, v___x_1815_, v___x_1816_, v___x_1817_, v_logOnUnused_1818_, v_fvars_1819_, v_x_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
stack->m_obj
 = v_res_1842_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed(lean_object* v_p_1843_, lean_object* v_type_1844_, lean_object* v_a_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v___x_1848_, lean_object* v_logOnUnused_1849_, lean_object* v_fvars_1850_, lean_object* v_x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_3493__boxed_1859_; lean_object* v_res_1860_; 
v___x_3493__boxed_1859_ = lean_unbox(v___x_1848_);
v_res_1860_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(v_p_1843_, v_type_1844_, v_a_1845_, v___x_1846_, v___x_1847_, v___x_3493__boxed_1859_, v_logOnUnused_1849_, v_fvars_1850_, v_x_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec_ref(v_x_1851_);
lean_dec_ref(v_fvars_1850_);
lean_dec(v___x_1847_);
lean_dec(v___x_1846_);
return v_res_1860_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(lean_object* v_decl_1861_, lean_object* v_p_1862_, lean_object* v_logOnUnused_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_type_1871_; lean_object* v___x_1872_; 
v_type_1871_ = lean_ctor_get(v_decl_1861_, 2);
lean_inc_ref_n(v_type_1871_, 2);
lean_dec_ref(v_decl_1861_);
lean_inc_ref(v_p_1862_);
v___x_1872_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_1862_, v_type_1871_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1896_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1896_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1896_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1877_ = lean_array_get_size(v_a_1873_);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_nat_sub(v___x_1877_, v___x_1878_);
v___x_1880_ = lean_nat_dec_lt(v___x_1879_, v___x_1877_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
lean_dec(v___x_1879_);
lean_dec(v_a_1873_);
lean_dec_ref(v_type_1871_);
lean_dec_ref(v_logOnUnused_1863_);
lean_dec_ref(v_p_1862_);
v___x_1881_ = lean_box(0);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1881_);
v___x_1883_ = v___x_1875_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
else
{
uint8_t v___x_1885_; 
v___x_1885_ = l_Lean_Expr_hasSorry(v_type_1871_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___f_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_del_object(v___x_1875_);
v___x_1886_ = lean_box(v___x_1885_);
lean_inc(v___x_1879_);
lean_inc(v_a_1873_);
lean_inc_ref(v_type_1871_);
v___f_1887_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed), 16, 7);
lean_closure_set(v___f_1887_, 0, v_p_1862_);
lean_closure_set(v___f_1887_, 1, v_type_1871_);
lean_closure_set(v___f_1887_, 2, v_a_1873_);
lean_closure_set(v___f_1887_, 3, v___x_1879_);
lean_closure_set(v___f_1887_, 4, v___x_1877_);
lean_closure_set(v___f_1887_, 5, v___x_1886_);
lean_closure_set(v___f_1887_, 6, v_logOnUnused_1863_);
v___x_1888_ = lean_array_fget(v_a_1873_, v___x_1879_);
lean_dec(v___x_1879_);
lean_dec(v_a_1873_);
v___x_1889_ = lean_nat_add(v___x_1888_, v___x_1878_);
lean_dec(v___x_1888_);
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
v___x_1891_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_1871_, v___x_1890_, v___f_1887_, v___x_1880_, v___x_1885_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_dec(v___x_1879_);
lean_dec(v_a_1873_);
lean_dec_ref(v_type_1871_);
lean_dec_ref(v_logOnUnused_1863_);
lean_dec_ref(v_p_1862_);
v___x_1892_ = lean_box(0);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1892_);
v___x_1894_ = v___x_1875_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v_type_1871_);
lean_dec_ref(v_logOnUnused_1863_);
lean_dec_ref(v_p_1862_);
v_a_1897_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1872_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1872_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1861_ = stack[0].m_obj;
lean_object* v_p_1862_ = stack[1].m_obj;
lean_object* v_logOnUnused_1863_ = stack[2].m_obj;
lean_object* v_a_1864_ = stack[3].m_obj;
lean_object* v_a_1865_ = stack[4].m_obj;
lean_object* v_a_1866_ = stack[5].m_obj;
lean_object* v_a_1867_ = stack[6].m_obj;
lean_object* v_a_1868_ = stack[7].m_obj;
lean_object* v_a_1869_ = stack[8].m_obj;
lean_object* v_res_1905_;
v_res_1905_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_decl_1861_, v_p_1862_, v_logOnUnused_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
stack->m_obj
 = v_res_1905_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___boxed(lean_object* v_decl_1906_, lean_object* v_p_1907_, lean_object* v_logOnUnused_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_decl_1906_, v_p_1907_, v_logOnUnused_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
return v_res_1916_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(lean_object* v___x_1917_, lean_object* v___x_1918_, lean_object* v___x_1919_, uint8_t v___x_1920_, lean_object* v_fvars_1921_, size_t v_sz_1922_, size_t v_i_1923_, lean_object* v_bs_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_1917_, v___x_1918_, v___x_1919_, v___x_1920_, v_fvars_1921_, v_sz_1922_, v_i_1923_, v_bs_1924_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1917_ = stack[0].m_obj;
lean_object* v___x_1918_ = stack[1].m_obj;
lean_object* v___x_1919_ = stack[2].m_obj;
uint8_t v___x_1920_ = stack[3].m_num;
lean_object* v_fvars_1921_ = stack[4].m_obj;
size_t v_sz_1922_ = stack[5].m_num;
size_t v_i_1923_ = stack[6].m_num;
lean_object* v_bs_1924_ = stack[7].m_obj;
lean_object* v___y_1925_ = stack[8].m_obj;
lean_object* v___y_1926_ = stack[9].m_obj;
lean_object* v___y_1927_ = stack[10].m_obj;
lean_object* v___y_1928_ = stack[11].m_obj;
lean_object* v___y_1929_ = stack[12].m_obj;
lean_object* v___y_1930_ = stack[13].m_obj;
lean_object* v_res_1933_;
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(v___x_1917_, v___x_1918_, v___x_1919_, v___x_1920_, v_fvars_1921_, v_sz_1922_, v_i_1923_, v_bs_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
stack->m_obj
 = v_res_1933_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___boxed(lean_object* v___x_1934_, lean_object* v___x_1935_, lean_object* v___x_1936_, lean_object* v___x_1937_, lean_object* v_fvars_1938_, lean_object* v_sz_1939_, lean_object* v_i_1940_, lean_object* v_bs_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v___x_3696__boxed_1949_; size_t v_sz_boxed_1950_; size_t v_i_boxed_1951_; lean_object* v_res_1952_; 
v___x_3696__boxed_1949_ = lean_unbox(v___x_1937_);
v_sz_boxed_1950_ = lean_unbox_usize(v_sz_1939_);
lean_dec(v_sz_1939_);
v_i_boxed_1951_ = lean_unbox_usize(v_i_1940_);
lean_dec(v_i_1940_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(v___x_1934_, v___x_1935_, v___x_1936_, v___x_3696__boxed_1949_, v_fvars_1938_, v_sz_boxed_1950_, v_i_boxed_1951_, v_bs_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec_ref(v_fvars_1938_);
lean_dec(v___x_1936_);
lean_dec(v___x_1935_);
lean_dec_ref(v___x_1934_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(lean_object* v_env_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
if (lean_obj_tag(v_a_1954_) == 0)
{
lean_object* v___x_1956_; 
lean_dec_ref(v_env_1953_);
v___x_1956_ = lean_array_to_list(v_a_1955_);
return v___x_1956_;
}
else
{
lean_object* v_head_1957_; lean_object* v_tail_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; 
v_head_1957_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_head_1957_);
v_tail_1958_ = lean_ctor_get(v_a_1954_, 1);
lean_inc(v_tail_1958_);
lean_dec_ref_known(v_a_1954_, 2);
v___x_1959_ = 0;
lean_inc_ref(v_env_1953_);
v___x_1960_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_1953_, v_head_1957_, v___x_1959_);
if (lean_obj_tag(v___x_1960_) == 0)
{
v_a_1954_ = v_tail_1958_;
goto _start;
}
else
{
lean_object* v_val_1962_; lean_object* v___x_1963_; 
v_val_1962_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_val_1962_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1963_ = lean_array_push(v_a_1955_, v_val_1962_);
v_a_1954_ = v_tail_1958_;
v_a_1955_ = v___x_1963_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(lean_object* v_t_1967_, lean_object* v_env_1968_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = l_Lean_Linter_getDeclsByBody(v_t_1967_);
v___x_1970_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0));
v___x_1971_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(v_env_1968_, v___x_1969_, v___x_1970_);
return v___x_1971_;
}
}
uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(lean_object* v_n_1990_){
_start:
{
uint8_t v___y_1992_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9));
v___x_2002_ = lean_name_eq(v_n_1990_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11));
v___x_2004_ = lean_name_eq(v_n_1990_, v___x_2003_);
v___y_1992_ = v___x_2004_;
goto v___jp_1991_;
}
else
{
v___y_1992_ = v___x_2002_;
goto v___jp_1991_;
}
v___jp_1991_:
{
if (v___y_1992_ == 0)
{
lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1));
v___x_1994_ = lean_name_eq(v_n_1990_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3));
v___x_1996_ = lean_name_eq(v_n_1990_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5));
v___x_1998_ = lean_name_eq(v_n_1990_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7));
v___x_2000_ = lean_name_eq(v_n_1990_, v___x_1999_);
return v___x_2000_;
}
else
{
return v___x_1998_;
}
}
else
{
return v___x_1996_;
}
}
else
{
return v___x_1994_;
}
}
else
{
return v___y_1992_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1990_ = stack[0].m_obj;
uint8_t v_res_2005_;
v_res_2005_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(v_n_1990_);
stack->m_num = v_res_2005_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___boxed(lean_object* v_n_2006_){
_start:
{
uint8_t v_res_2007_; lean_object* v_r_2008_; 
v_res_2007_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(v_n_2006_);
lean_dec(v_n_2006_);
v_r_2008_ = lean_box(v_res_2007_);
return v_r_2008_;
}
}
uint8_t l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(lean_object* v_type_2010_){
_start:
{
lean_object* v___f_2011_; uint8_t v___x_2012_; 
v___f_2011_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0));
v___x_2012_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(v___f_2011_, v_type_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2010_ = stack[0].m_obj;
uint8_t v_res_2013_;
v_res_2013_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(v_type_2010_);
stack->m_num = v_res_2013_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___boxed(lean_object* v_type_2014_){
_start:
{
uint8_t v_res_2015_; lean_object* v_r_2016_; 
v_res_2015_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(v_type_2014_);
v_r_2016_ = lean_box(v_res_2015_);
return v_r_2016_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(lean_object* v___y_2017_){
_start:
{
lean_object* v___x_2019_; lean_object* v_infoState_2020_; lean_object* v_trees_2021_; lean_object* v___x_2022_; 
v___x_2019_ = lean_st_ref_get(v___y_2017_);
v_infoState_2020_ = lean_ctor_get(v___x_2019_, 8);
lean_inc_ref(v_infoState_2020_);
lean_dec(v___x_2019_);
v_trees_2021_ = lean_ctor_get(v_infoState_2020_, 2);
lean_inc_ref(v_trees_2021_);
lean_dec_ref(v_infoState_2020_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_trees_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2017_ = stack[0].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_2017_);
stack->m_obj
 = v_res_2023_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg___boxed(lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_2024_);
lean_dec(v___y_2024_);
return v_res_2026_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2027_ = stack[0].m_obj;
lean_object* v___y_2028_ = stack[1].m_obj;
lean_object* v_res_2031_;
v_res_2031_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(v___y_2027_, v___y_2028_);
stack->m_obj
 = v_res_2031_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___boxed(lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2035_;
}
}
lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(uint8_t v___x_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
if (lean_obj_tag(v_a_2038_) == 0)
{
lean_object* v___x_2040_; 
v___x_2040_ = l_List_reverse___redArg(v_a_2039_);
return v___x_2040_;
}
else
{
lean_object* v_head_2041_; lean_object* v_tail_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2060_; 
v_head_2041_ = lean_ctor_get(v_a_2038_, 0);
v_tail_2042_ = lean_ctor_get(v_a_2038_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2044_ = v_a_2038_;
v_isShared_2045_ = v_isSharedCheck_2060_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_tail_2042_);
lean_inc(v_head_2041_);
lean_dec(v_a_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2060_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_name_2046_; lean_object* v_type_2047_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_name_2046_ = lean_ctor_get(v_head_2041_, 0);
v_type_2047_ = lean_ctor_get(v_head_2041_, 2);
v___x_2056_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9));
lean_inc(v_name_2046_);
v___x_2057_ = l_Lean_privateToUserName(v_name_2046_);
v___x_2058_ = l_Lean_Name_isPrefixOf(v___x_2056_, v___x_2057_);
lean_dec(v___x_2057_);
if (v___x_2058_ == 0)
{
goto v___jp_2048_;
}
else
{
if (v___x_2037_ == 0)
{
lean_del_object(v___x_2044_);
lean_dec(v_head_2041_);
v_a_2038_ = v_tail_2042_;
goto _start;
}
else
{
goto v___jp_2048_;
}
}
v___jp_2048_:
{
lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2049_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0));
lean_inc_ref(v_type_2047_);
v___x_2050_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(v___x_2049_, v_type_2047_);
if (v___x_2050_ == 0)
{
lean_del_object(v___x_2044_);
lean_dec(v_head_2041_);
v_a_2038_ = v_tail_2042_;
goto _start;
}
else
{
lean_object* v___x_2053_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v_a_2039_);
v___x_2053_ = v___x_2044_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_head_2041_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_a_2039_);
v___x_2053_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
v_a_2038_ = v_tail_2042_;
v_a_2039_ = v___x_2053_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2037_ = stack[0].m_num;
lean_object* v_a_2038_ = stack[1].m_obj;
lean_object* v_a_2039_ = stack[2].m_obj;
lean_object* v_res_2061_;
v_res_2061_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2037_, v_a_2038_, v_a_2039_);
stack->m_obj
 = v_res_2061_;
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___boxed(lean_object* v___x_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
uint8_t v___x_11555__boxed_2065_; lean_object* v_res_2066_; 
v___x_11555__boxed_2065_ = lean_unbox(v___x_2062_);
v_res_2066_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_11555__boxed_2065_, v_a_2063_, v_a_2064_);
return v_res_2066_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(lean_object* v_o_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_env_2072_; lean_object* v___x_2073_; lean_object* v_toEnvExtension_2074_; lean_object* v_asyncMode_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v_merged_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2087_; 
v___x_2070_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2071_ = lean_st_ref_get(v___y_2068_);
v_env_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc_ref(v_env_2072_);
lean_dec(v___x_2071_);
v___x_2073_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2074_ = lean_ctor_get(v___x_2073_, 0);
v_asyncMode_2075_ = lean_ctor_get(v_toEnvExtension_2074_, 2);
v___x_2076_ = lean_box(0);
v___x_2077_ = 0;
v___x_2078_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2070_, v___x_2073_, v_env_2072_, v_asyncMode_2075_, v___x_2076_, v___x_2077_);
v_merged_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2078_, 1);
lean_dec(v_unused_2088_);
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_merged_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v_merged_2079_);
lean_ctor_set(v___x_2081_, 0, v_o_2067_);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_o_2067_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_merged_2079_);
v___x_2084_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2067_ = stack[0].m_obj;
lean_object* v___y_2068_ = stack[1].m_obj;
lean_object* v_res_2089_;
v_res_2089_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_o_2067_, v___y_2068_);
stack->m_obj
 = v_res_2089_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_o_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_o_2090_, v___y_2091_);
lean_dec(v___y_2091_);
return v_res_2093_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2098_);
v___x_2102_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v___x_2101_, v___y_2099_);
return v___x_2102_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2094_ = stack[0].m_obj;
lean_object* v___y_2095_ = stack[1].m_obj;
lean_object* v___y_2096_ = stack[2].m_obj;
lean_object* v___y_2097_ = stack[3].m_obj;
lean_object* v___y_2098_ = stack[4].m_obj;
lean_object* v___y_2099_ = stack[5].m_obj;
lean_object* v_res_2103_;
v_res_2103_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
stack->m_obj
 = v_res_2103_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3___boxed(lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2111_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(lean_object* v_msgData_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v_env_2119_; uint8_t v___x_2120_; lean_object* v_env_2121_; lean_object* v___x_2122_; lean_object* v_toCold_2123_; lean_object* v_mctx_2124_; lean_object* v_lctx_2125_; lean_object* v_options_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2118_ = lean_st_ref_get(v___y_2116_);
v_env_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc_ref(v_env_2119_);
lean_dec(v___x_2118_);
v___x_2120_ = 0;
v_env_2121_ = l_Lean_Environment_setRecordingDeps(v_env_2119_, v___x_2120_);
v___x_2122_ = lean_st_ref_get(v___y_2114_);
v_toCold_2123_ = lean_ctor_get(v___y_2115_, 0);
v_mctx_2124_ = lean_ctor_get(v___x_2122_, 0);
lean_inc_ref(v_mctx_2124_);
lean_dec(v___x_2122_);
v_lctx_2125_ = lean_ctor_get(v___y_2113_, 2);
v_options_2126_ = lean_ctor_get(v_toCold_2123_, 2);
lean_inc_ref(v_options_2126_);
lean_inc_ref(v_lctx_2125_);
v___x_2127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2127_, 0, v_env_2121_);
lean_ctor_set(v___x_2127_, 1, v_mctx_2124_);
lean_ctor_set(v___x_2127_, 2, v_lctx_2125_);
lean_ctor_set(v___x_2127_, 3, v_options_2126_);
v___x_2128_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_msgData_2112_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2112_ = stack[0].m_obj;
lean_object* v___y_2113_ = stack[1].m_obj;
lean_object* v___y_2114_ = stack[2].m_obj;
lean_object* v___y_2115_ = stack[3].m_obj;
lean_object* v___y_2116_ = stack[4].m_obj;
lean_object* v_res_2130_;
v_res_2130_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(v_msgData_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
stack->m_obj
 = v_res_2130_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13___boxed(lean_object* v_msgData_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(v_msgData_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2137_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(lean_object* v_opts_2138_, lean_object* v_opt_2139_){
_start:
{
lean_object* v_name_2140_; lean_object* v_defValue_2141_; lean_object* v_map_2142_; lean_object* v___x_2143_; 
v_name_2140_ = lean_ctor_get(v_opt_2139_, 0);
v_defValue_2141_ = lean_ctor_get(v_opt_2139_, 1);
v_map_2142_ = lean_ctor_get(v_opts_2138_, 0);
v___x_2143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2142_, v_name_2140_);
if (lean_obj_tag(v___x_2143_) == 0)
{
uint8_t v___x_2144_; 
v___x_2144_ = lean_unbox(v_defValue_2141_);
return v___x_2144_;
}
else
{
lean_object* v_val_2145_; 
v_val_2145_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_val_2145_) == 1)
{
uint8_t v_v_2146_; 
v_v_2146_ = lean_ctor_get_uint8(v_val_2145_, 0);
lean_dec_ref_known(v_val_2145_, 0);
return v_v_2146_;
}
else
{
uint8_t v___x_2147_; 
lean_dec(v_val_2145_);
v___x_2147_ = lean_unbox(v_defValue_2141_);
return v___x_2147_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2138_ = stack[0].m_obj;
lean_object* v_opt_2139_ = stack[1].m_obj;
uint8_t v_res_2148_;
v_res_2148_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(v_opts_2138_, v_opt_2139_);
stack->m_num = v_res_2148_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14___boxed(lean_object* v_opts_2149_, lean_object* v_opt_2150_){
_start:
{
uint8_t v_res_2151_; lean_object* v_r_2152_; 
v_res_2151_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(v_opts_2149_, v_opt_2150_);
lean_dec_ref(v_opt_2150_);
lean_dec_ref(v_opts_2149_);
v_r_2152_ = lean_box(v_res_2151_);
return v_r_2152_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(uint8_t v_suppressElabErrors_2161_, uint8_t v___y_2162_, lean_object* v_x_2163_){
_start:
{
if (lean_obj_tag(v_x_2163_) == 1)
{
lean_object* v_pre_2164_; 
v_pre_2164_ = lean_ctor_get(v_x_2163_, 0);
switch(lean_obj_tag(v_pre_2164_))
{
case 1:
{
lean_object* v_pre_2165_; 
v_pre_2165_ = lean_ctor_get(v_pre_2164_, 0);
switch(lean_obj_tag(v_pre_2165_))
{
case 0:
{
lean_object* v_str_2166_; lean_object* v_str_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v_str_2166_ = lean_ctor_get(v_x_2163_, 1);
v_str_2167_ = lean_ctor_get(v_pre_2164_, 1);
v___x_2168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__0));
v___x_2169_ = lean_string_dec_eq(v_str_2167_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__1));
v___x_2171_ = lean_string_dec_eq(v_str_2167_, v___x_2170_);
if (v___x_2171_ == 0)
{
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__2));
v___x_2173_ = lean_string_dec_eq(v_str_2166_, v___x_2172_);
if (v___x_2173_ == 0)
{
return v___x_2173_;
}
else
{
return v_suppressElabErrors_2161_;
}
}
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__3));
v___x_2175_ = lean_string_dec_eq(v_str_2166_, v___x_2174_);
if (v___x_2175_ == 0)
{
return v___x_2175_;
}
else
{
return v_suppressElabErrors_2161_;
}
}
}
case 1:
{
lean_object* v_pre_2176_; 
v_pre_2176_ = lean_ctor_get(v_pre_2165_, 0);
if (lean_obj_tag(v_pre_2176_) == 0)
{
lean_object* v_str_2177_; lean_object* v_str_2178_; lean_object* v_str_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v_str_2177_ = lean_ctor_get(v_x_2163_, 1);
v_str_2178_ = lean_ctor_get(v_pre_2164_, 1);
v_str_2179_ = lean_ctor_get(v_pre_2165_, 1);
v___x_2180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__4));
v___x_2181_ = lean_string_dec_eq(v_str_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__5));
v___x_2183_ = lean_string_dec_eq(v_str_2178_, v___x_2182_);
if (v___x_2183_ == 0)
{
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__6));
v___x_2185_ = lean_string_dec_eq(v_str_2177_, v___x_2184_);
if (v___x_2185_ == 0)
{
return v___x_2185_;
}
else
{
return v_suppressElabErrors_2161_;
}
}
}
}
else
{
return v___y_2162_;
}
}
default: 
{
return v___y_2162_;
}
}
}
case 0:
{
lean_object* v_str_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_str_2186_ = lean_ctor_get(v_x_2163_, 1);
v___x_2187_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___closed__7));
v___x_2188_ = lean_string_dec_eq(v_str_2186_, v___x_2187_);
if (v___x_2188_ == 0)
{
return v___x_2188_;
}
else
{
return v_suppressElabErrors_2161_;
}
}
default: 
{
return v___y_2162_;
}
}
}
else
{
return v___y_2162_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_2161_ = stack[0].m_num;
uint8_t v___y_2162_ = stack[1].m_num;
lean_object* v_x_2163_ = stack[2].m_obj;
uint8_t v_res_2189_;
v_res_2189_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(v_suppressElabErrors_2161_, v___y_2162_, v_x_2163_);
stack->m_num = v_res_2189_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2190_, lean_object* v___y_2191_, lean_object* v_x_2192_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2193_; uint8_t v___y_11799__boxed_2194_; uint8_t v_res_2195_; lean_object* v_r_2196_; 
v_suppressElabErrors_boxed_2193_ = lean_unbox(v_suppressElabErrors_2190_);
v___y_11799__boxed_2194_ = lean_unbox(v___y_2191_);
v_res_2195_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0(v_suppressElabErrors_boxed_2193_, v___y_11799__boxed_2194_, v_x_2192_);
lean_dec(v_x_2192_);
v_r_2196_ = lean_box(v_res_2195_);
return v_r_2196_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(lean_object* v_ref_2197_, lean_object* v_msgData_2198_, uint8_t v_severity_2199_, uint8_t v_isSilent_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___y_2207_; uint8_t v___y_2208_; uint8_t v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v_toCold_2214_; lean_object* v___y_2215_; lean_object* v___y_2244_; lean_object* v___y_2245_; uint8_t v___y_2246_; uint8_t v___y_2247_; lean_object* v___y_2248_; uint8_t v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; uint8_t v___y_2275_; uint8_t v___y_2276_; lean_object* v___y_2277_; uint8_t v___y_2281_; uint8_t v___y_2282_; uint8_t v___y_2283_; uint8_t v___x_2294_; uint8_t v___y_2296_; uint8_t v___y_2297_; uint8_t v___y_2298_; uint8_t v___y_2300_; uint8_t v___x_2308_; 
v___x_2294_ = 2;
v___x_2308_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2199_, v___x_2294_);
if (v___x_2308_ == 0)
{
v___y_2300_ = v___x_2308_;
goto v___jp_2299_;
}
else
{
uint8_t v___x_2309_; 
lean_inc_ref(v_msgData_2198_);
v___x_2309_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2198_);
v___y_2300_ = v___x_2309_;
goto v___jp_2299_;
}
v___jp_2206_:
{
lean_object* v_currNamespace_2216_; lean_object* v_openDecls_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_env_2222_; lean_object* v_nextMacroScope_2223_; lean_object* v_ngen_2224_; lean_object* v_auxDeclNGen_2225_; lean_object* v_traceState_2226_; lean_object* v_cache_2227_; lean_object* v_recordedDeps_2228_; lean_object* v_messages_2229_; lean_object* v_infoState_2230_; lean_object* v_snapshotTasks_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
v_currNamespace_2216_ = lean_ctor_get(v_toCold_2214_, 4);
v_openDecls_2217_ = lean_ctor_get(v_toCold_2214_, 5);
lean_inc(v_openDecls_2217_);
lean_inc(v_currNamespace_2216_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_currNamespace_2216_);
lean_ctor_set(v___x_2218_, 1, v_openDecls_2217_);
v___x_2219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___y_2212_);
lean_inc_ref(v___y_2210_);
lean_inc_ref(v___y_2213_);
v___x_2220_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2220_, 0, v___y_2213_);
lean_ctor_set(v___x_2220_, 1, v___y_2211_);
lean_ctor_set(v___x_2220_, 2, v___y_2207_);
lean_ctor_set(v___x_2220_, 3, v___y_2210_);
lean_ctor_set(v___x_2220_, 4, v___x_2219_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*5, v___y_2208_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*5 + 1, v___y_2209_);
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*5 + 2, v_isSilent_2200_);
v___x_2221_ = lean_st_ref_take(v___y_2215_);
v_env_2222_ = lean_ctor_get(v___x_2221_, 0);
v_nextMacroScope_2223_ = lean_ctor_get(v___x_2221_, 1);
v_ngen_2224_ = lean_ctor_get(v___x_2221_, 2);
v_auxDeclNGen_2225_ = lean_ctor_get(v___x_2221_, 3);
v_traceState_2226_ = lean_ctor_get(v___x_2221_, 4);
v_cache_2227_ = lean_ctor_get(v___x_2221_, 5);
v_recordedDeps_2228_ = lean_ctor_get(v___x_2221_, 6);
v_messages_2229_ = lean_ctor_get(v___x_2221_, 7);
v_infoState_2230_ = lean_ctor_get(v___x_2221_, 8);
v_snapshotTasks_2231_ = lean_ctor_get(v___x_2221_, 9);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2233_ = v___x_2221_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_snapshotTasks_2231_);
lean_inc(v_infoState_2230_);
lean_inc(v_messages_2229_);
lean_inc(v_recordedDeps_2228_);
lean_inc(v_cache_2227_);
lean_inc(v_traceState_2226_);
lean_inc(v_auxDeclNGen_2225_);
lean_inc(v_ngen_2224_);
lean_inc(v_nextMacroScope_2223_);
lean_inc(v_env_2222_);
lean_dec(v___x_2221_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = l_Lean_MessageLog_add(v___x_2220_, v_messages_2229_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 7, v___x_2236_);
v___x_2238_ = v___x_2233_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_env_2222_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_nextMacroScope_2223_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_ngen_2224_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_auxDeclNGen_2225_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_traceState_2226_);
lean_ctor_set(v_reuseFailAlloc_2241_, 5, v_cache_2227_);
lean_ctor_set(v_reuseFailAlloc_2241_, 6, v_recordedDeps_2228_);
lean_ctor_set(v_reuseFailAlloc_2241_, 7, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2241_, 8, v_infoState_2230_);
lean_ctor_set(v_reuseFailAlloc_2241_, 9, v_snapshotTasks_2231_);
v___x_2238_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_st_ref_put(v___y_2215_, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2235_);
return v___x_2240_;
}
}
}
v___jp_2243_:
{
lean_object* v_fileName_2252_; lean_object* v_fileMap_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2269_; 
v_fileName_2252_ = lean_ctor_get(v___y_2248_, 0);
v_fileMap_2253_ = lean_ctor_get(v___y_2248_, 1);
v___x_2254_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2198_);
v___x_2255_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__13(v___x_2254_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2269_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2269_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_inc_ref_n(v_fileMap_2253_, 2);
v___x_2260_ = l_Lean_FileMap_toPosition(v_fileMap_2253_, v___y_2250_);
lean_dec(v___y_2250_);
v___x_2261_ = l_Lean_FileMap_toPosition(v_fileMap_2253_, v___y_2251_);
lean_dec(v___y_2251_);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
v___x_2263_ = ((lean_object*)(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4));
if (v___y_2246_ == 0)
{
lean_del_object(v___x_2258_);
lean_dec_ref(v___y_2244_);
v___y_2207_ = v___x_2262_;
v___y_2208_ = v___y_2247_;
v___y_2209_ = v___y_2249_;
v___y_2210_ = v___x_2263_;
v___y_2211_ = v___x_2260_;
v___y_2212_ = v_a_2256_;
v___y_2213_ = v_fileName_2252_;
v_toCold_2214_ = v___y_2245_;
v___y_2215_ = v___y_2204_;
goto v___jp_2206_;
}
else
{
uint8_t v___x_2264_; 
lean_inc(v_a_2256_);
v___x_2264_ = l_Lean_MessageData_hasTag(v___y_2244_, v_a_2256_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_dec_ref_known(v___x_2262_, 1);
lean_dec_ref(v___x_2260_);
lean_dec(v_a_2256_);
v___x_2265_ = lean_box(0);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2265_);
v___x_2267_ = v___x_2258_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
else
{
lean_del_object(v___x_2258_);
v___y_2207_ = v___x_2262_;
v___y_2208_ = v___y_2247_;
v___y_2209_ = v___y_2249_;
v___y_2210_ = v___x_2263_;
v___y_2211_ = v___x_2260_;
v___y_2212_ = v_a_2256_;
v___y_2213_ = v_fileName_2252_;
v_toCold_2214_ = v___y_2245_;
v___y_2215_ = v___y_2204_;
goto v___jp_2206_;
}
}
}
}
v___jp_2270_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Syntax_getTailPos_x3f(v___y_2274_, v___y_2275_);
lean_dec(v___y_2274_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_inc(v___y_2277_);
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2273_;
v___y_2246_ = v___y_2271_;
v___y_2247_ = v___y_2275_;
v___y_2248_ = v___y_2273_;
v___y_2249_ = v___y_2276_;
v___y_2250_ = v___y_2277_;
v___y_2251_ = v___y_2277_;
goto v___jp_2243_;
}
else
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2273_;
v___y_2246_ = v___y_2271_;
v___y_2247_ = v___y_2275_;
v___y_2248_ = v___y_2273_;
v___y_2249_ = v___y_2276_;
v___y_2250_ = v___y_2277_;
v___y_2251_ = v_val_2279_;
goto v___jp_2243_;
}
}
v___jp_2280_:
{
lean_object* v_toCold_2284_; lean_object* v_ref_2285_; uint8_t v_suppressElabErrors_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v_ref_2290_; lean_object* v___x_2291_; 
v_toCold_2284_ = lean_ctor_get(v___y_2203_, 0);
v_ref_2285_ = lean_ctor_get(v___y_2203_, 2);
v_suppressElabErrors_2286_ = lean_ctor_get_uint8(v___y_2203_, sizeof(void*)*3 + 2);
v___x_2287_ = lean_box(v_suppressElabErrors_2286_);
v___x_2288_ = lean_box(v___y_2281_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2289_, 0, v___x_2287_);
lean_closure_set(v___f_2289_, 1, v___x_2288_);
v_ref_2290_ = l_Lean_replaceRef(v_ref_2197_, v_ref_2285_);
v___x_2291_ = l_Lean_Syntax_getPos_x3f(v_ref_2290_, v___y_2282_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_unsigned_to_nat(0u);
v___y_2271_ = v_suppressElabErrors_2286_;
v___y_2272_ = v___f_2289_;
v___y_2273_ = v_toCold_2284_;
v___y_2274_ = v_ref_2290_;
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v___x_2292_;
goto v___jp_2270_;
}
else
{
lean_object* v_val_2293_; 
v_val_2293_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v___x_2291_, 1);
v___y_2271_ = v_suppressElabErrors_2286_;
v___y_2272_ = v___f_2289_;
v___y_2273_ = v_toCold_2284_;
v___y_2274_ = v_ref_2290_;
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v_val_2293_;
goto v___jp_2270_;
}
}
v___jp_2295_:
{
if (v___y_2298_ == 0)
{
v___y_2281_ = v___y_2296_;
v___y_2282_ = v___y_2297_;
v___y_2283_ = v_severity_2199_;
goto v___jp_2280_;
}
else
{
v___y_2281_ = v___y_2296_;
v___y_2282_ = v___y_2297_;
v___y_2283_ = v___x_2294_;
goto v___jp_2280_;
}
}
v___jp_2299_:
{
if (v___y_2300_ == 0)
{
uint8_t v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = 1;
v___x_2302_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2199_, v___x_2301_);
if (v___x_2302_ == 0)
{
v___y_2296_ = v___y_2300_;
v___y_2297_ = v___y_2300_;
v___y_2298_ = v___x_2302_;
goto v___jp_2295_;
}
else
{
lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2303_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2203_);
v___x_2304_ = l_Lean_warningAsError;
v___x_2305_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_spec__14(v___x_2303_, v___x_2304_);
lean_dec_ref(v___x_2303_);
v___y_2296_ = v___y_2300_;
v___y_2297_ = v___y_2300_;
v___y_2298_ = v___x_2305_;
goto v___jp_2295_;
}
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_msgData_2198_);
v___x_2306_ = lean_box(0);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2197_ = stack[0].m_obj;
lean_object* v_msgData_2198_ = stack[1].m_obj;
uint8_t v_severity_2199_ = stack[2].m_num;
uint8_t v_isSilent_2200_ = stack[3].m_num;
lean_object* v___y_2201_ = stack[4].m_obj;
lean_object* v___y_2202_ = stack[5].m_obj;
lean_object* v___y_2203_ = stack[6].m_obj;
lean_object* v___y_2204_ = stack[7].m_obj;
lean_object* v_res_2310_;
v_res_2310_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2197_, v_msgData_2198_, v_severity_2199_, v_isSilent_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
stack->m_obj
 = v_res_2310_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg___boxed(lean_object* v_ref_2311_, lean_object* v_msgData_2312_, lean_object* v_severity_2313_, lean_object* v_isSilent_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
uint8_t v_severity_boxed_2320_; uint8_t v_isSilent_boxed_2321_; lean_object* v_res_2322_; 
v_severity_boxed_2320_ = lean_unbox(v_severity_2313_);
v_isSilent_boxed_2321_ = lean_unbox(v_isSilent_2314_);
v_res_2322_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2311_, v_msgData_2312_, v_severity_boxed_2320_, v_isSilent_boxed_2321_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v_ref_2311_);
return v_res_2322_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(lean_object* v_ref_2323_, lean_object* v_msgData_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = 1;
v___x_2333_ = 0;
v___x_2334_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_2323_, v_msgData_2324_, v___x_2332_, v___x_2333_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v___x_2334_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2323_ = stack[0].m_obj;
lean_object* v_msgData_2324_ = stack[1].m_obj;
lean_object* v___y_2325_ = stack[2].m_obj;
lean_object* v___y_2326_ = stack[3].m_obj;
lean_object* v___y_2327_ = stack[4].m_obj;
lean_object* v___y_2328_ = stack[5].m_obj;
lean_object* v___y_2329_ = stack[6].m_obj;
lean_object* v___y_2330_ = stack[7].m_obj;
lean_object* v_res_2335_;
v_res_2335_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(v_ref_2323_, v_msgData_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
stack->m_obj
 = v_res_2335_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6___boxed(lean_object* v_ref_2336_, lean_object* v_msgData_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(v_ref_2336_, v_msgData_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v_ref_2336_);
return v_res_2345_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__0));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__2));
v___x_2351_ = l_Lean_stringToMessageData(v___x_2350_);
return v___x_2351_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(lean_object* v_linterOption_2352_, lean_object* v_stx_2353_, lean_object* v_msg_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_name_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2380_; 
v_name_2362_ = lean_ctor_get(v_linterOption_2352_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_linterOption_2352_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; 
v_unused_2381_ = lean_ctor_get(v_linterOption_2352_, 1);
lean_dec(v_unused_2381_);
v___x_2364_ = v_linterOption_2352_;
v_isShared_2365_ = v_isSharedCheck_2380_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_name_2362_);
lean_dec(v_linterOption_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2380_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__1);
lean_inc(v_name_2362_);
v___x_2367_ = l_Lean_MessageData_ofName(v_name_2362_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 7);
lean_ctor_set(v___x_2364_, 1, v___x_2367_);
lean_ctor_set(v___x_2364_, 0, v___x_2366_);
v___x_2369_ = v___x_2364_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v_disable_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2370_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___closed__3);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v_disable_2372_ = l_Lean_MessageData_note(v___x_2371_);
v___x_2373_ = l_Lean_Linter_linterMessageTag;
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_msg_2354_);
lean_ctor_set(v___x_2374_, 1, v_disable_2372_);
v___x_2375_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2376_, 0, v_name_2362_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
lean_inc(v_stx_2353_);
v___x_2377_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_stx_2353_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6(v_stx_2353_, v___x_2377_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v_stx_2353_);
return v___x_2378_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_2352_ = stack[0].m_obj;
lean_object* v_stx_2353_ = stack[1].m_obj;
lean_object* v_msg_2354_ = stack[2].m_obj;
lean_object* v___y_2355_ = stack[3].m_obj;
lean_object* v___y_2356_ = stack[4].m_obj;
lean_object* v___y_2357_ = stack[5].m_obj;
lean_object* v___y_2358_ = stack[6].m_obj;
lean_object* v___y_2359_ = stack[7].m_obj;
lean_object* v___y_2360_ = stack[8].m_obj;
lean_object* v_res_2382_;
v_res_2382_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(v_linterOption_2352_, v_stx_2353_, v_msg_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
stack->m_obj
 = v_res_2382_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4___boxed(lean_object* v_linterOption_2383_, lean_object* v_stx_2384_, lean_object* v_msg_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(v_linterOption_2383_, v_stx_2384_, v_msg_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
return v_res_2393_;
}
}
lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(lean_object* v_linterOption_2394_, lean_object* v_stx_2395_, lean_object* v_msg_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2415_; 
v___x_2404_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3(v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2415_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2415_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
uint8_t v___x_2409_; 
v___x_2409_ = l_Lean_Linter_getLinterValue(v_linterOption_2394_, v_a_2405_);
lean_dec(v_a_2405_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_dec_ref(v_msg_2396_);
lean_dec(v_stx_2395_);
lean_dec_ref(v_linterOption_2394_);
v___x_2410_ = lean_box(0);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2410_);
v___x_2412_ = v___x_2407_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
else
{
lean_object* v___x_2414_; 
lean_del_object(v___x_2407_);
v___x_2414_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4(v_linterOption_2394_, v_stx_2395_, v_msg_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_2394_ = stack[0].m_obj;
lean_object* v_stx_2395_ = stack[1].m_obj;
lean_object* v_msg_2396_ = stack[2].m_obj;
lean_object* v___y_2397_ = stack[3].m_obj;
lean_object* v___y_2398_ = stack[4].m_obj;
lean_object* v___y_2399_ = stack[5].m_obj;
lean_object* v___y_2400_ = stack[6].m_obj;
lean_object* v___y_2401_ = stack[7].m_obj;
lean_object* v___y_2402_ = stack[8].m_obj;
lean_object* v_res_2416_;
v_res_2416_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v_linterOption_2394_, v_stx_2395_, v_msg_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
stack->m_obj
 = v_res_2416_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___boxed(lean_object* v_linterOption_2417_, lean_object* v_stx_2418_, lean_object* v_msg_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v_linterOption_2417_, v_stx_2418_, v_msg_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2427_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0));
v___x_2430_ = l_Lean_stringToMessageData(v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(lean_object* v_head_2436_, lean_object* v___x_2437_, lean_object* v_unusedParams_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_ref_2446_; lean_object* v_name_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___y_2452_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v_ref_2446_ = lean_ctor_get(v___y_2443_, 2);
v_name_2447_ = lean_ctor_get(v_head_2436_, 0);
lean_inc(v_name_2447_);
lean_dec_ref(v_head_2436_);
lean_inc_ref(v_unusedParams_2438_);
v___x_2448_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(v_name_2447_, v_unusedParams_2438_);
v___x_2449_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1);
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2458_ = lean_array_get_size(v_unusedParams_2438_);
lean_dec_ref(v_unusedParams_2438_);
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = lean_nat_dec_eq(v___x_2458_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4));
v___y_2452_ = v___x_2461_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2462_; 
v___x_2462_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5));
v___y_2452_ = v___x_2462_;
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_inc_ref(v___y_2452_);
v___x_2453_ = l_Lean_stringToMessageData(v___y_2452_);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2450_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
lean_inc(v_ref_2446_);
v___x_2457_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_2437_, v_ref_2446_, v___x_2456_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2457_;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_2436_ = stack[0].m_obj;
lean_object* v___x_2437_ = stack[1].m_obj;
lean_object* v_unusedParams_2438_ = stack[2].m_obj;
lean_object* v___y_2439_ = stack[3].m_obj;
lean_object* v___y_2440_ = stack[4].m_obj;
lean_object* v___y_2441_ = stack[5].m_obj;
lean_object* v___y_2442_ = stack[6].m_obj;
lean_object* v___y_2443_ = stack[7].m_obj;
lean_object* v___y_2444_ = stack[8].m_obj;
lean_object* v_res_2463_;
v_res_2463_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(v_head_2436_, v___x_2437_, v_unusedParams_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
stack->m_obj
 = v_res_2463_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed(lean_object* v_head_2464_, lean_object* v___x_2465_, lean_object* v_unusedParams_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(v_head_2464_, v___x_2465_, v_unusedParams_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2474_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(lean_object* v_as_x27_2475_, lean_object* v_b_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
if (lean_obj_tag(v_as_x27_2475_) == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_b_2476_);
return v___x_2484_;
}
else
{
lean_object* v_head_2485_; lean_object* v_tail_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_head_2485_ = lean_ctor_get(v_as_x27_2475_, 0);
v_tail_2486_ = lean_ctor_get(v_as_x27_2475_, 1);
v___x_2487_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
v___x_2488_ = lean_box(0);
lean_inc_n(v_head_2485_, 2);
v___f_2489_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_2489_, 0, v_head_2485_);
lean_closure_set(v___f_2489_, 1, v___x_2487_);
v___x_2490_ = ((lean_object*)(l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___closed__0));
v___x_2491_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_head_2485_, v___x_2490_, v___f_2489_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_dec_ref_known(v___x_2491_, 1);
v_as_x27_2475_ = v_tail_2486_;
v_b_2476_ = v___x_2488_;
goto _start;
}
else
{
return v___x_2491_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2475_ = stack[0].m_obj;
lean_object* v_b_2476_ = stack[1].m_obj;
lean_object* v___y_2477_ = stack[2].m_obj;
lean_object* v___y_2478_ = stack[3].m_obj;
lean_object* v___y_2479_ = stack[4].m_obj;
lean_object* v___y_2480_ = stack[5].m_obj;
lean_object* v___y_2481_ = stack[6].m_obj;
lean_object* v___y_2482_ = stack[7].m_obj;
lean_object* v_res_2493_;
v_res_2493_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_2475_, v_b_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
stack->m_obj
 = v_res_2493_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___boxed(lean_object* v_as_x27_2494_, lean_object* v_b_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_2494_, v_b_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v_as_x27_2494_);
return v_res_2503_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(lean_object* v___x_2504_, lean_object* v___x_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v___x_2504_, v___x_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v___x_2513_, 0);
lean_dec(v_unused_2521_);
v___x_2515_ = v___x_2513_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_dec(v___x_2513_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2505_);
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2505_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
return v___x_2513_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2504_ = stack[0].m_obj;
lean_object* v___x_2505_ = stack[1].m_obj;
lean_object* v___y_2506_ = stack[2].m_obj;
lean_object* v___y_2507_ = stack[3].m_obj;
lean_object* v___y_2508_ = stack[4].m_obj;
lean_object* v___y_2509_ = stack[5].m_obj;
lean_object* v___y_2510_ = stack[6].m_obj;
lean_object* v___y_2511_ = stack[7].m_obj;
lean_object* v_res_2522_;
v_res_2522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(v___x_2504_, v___x_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
stack->m_obj
 = v_res_2522_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed(lean_object* v___x_2523_, lean_object* v___x_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(v___x_2523_, v___x_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___x_2523_);
return v_res_2532_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(lean_object* v___x_2533_, uint8_t v___x_2534_, lean_object* v_as_2535_, size_t v_sz_2536_, size_t v_i_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_usize_dec_lt(v_i_2537_, v_sz_2536_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
lean_dec_ref(v___x_2533_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_b_2538_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v_a_2546_; lean_object* v___x_2551_; lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
lean_dec_ref(v_b_2538_);
v___x_2544_ = lean_box(0);
v___x_2551_ = lean_box(0);
v_a_2552_ = lean_array_uget_borrowed(v_as_2535_, v_i_2537_);
lean_inc_ref(v___x_2533_);
lean_inc(v_a_2552_);
v___x_2553_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2552_, v___x_2533_);
v___x_2554_ = lean_box(0);
v___x_2555_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2534_, v___x_2553_, v___x_2554_);
v___x_2556_ = l_List_isEmpty___redArg(v___x_2555_);
if (v___x_2556_ == 0)
{
lean_object* v___f_2557_; lean_object* v___x_2558_; 
v___f_2557_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2557_, 0, v___x_2555_);
lean_closure_set(v___f_2557_, 1, v___x_2551_);
v___x_2558_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2557_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref_known(v___x_2558_, 1);
v_a_2546_ = v___x_2551_;
goto v___jp_2545_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___x_2533_);
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_dec(v___x_2555_);
v_a_2546_ = v___x_2551_;
goto v___jp_2545_;
}
v___jp_2545_:
{
lean_object* v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; 
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2544_);
lean_ctor_set(v___x_2547_, 1, v_a_2546_);
v___x_2548_ = ((size_t)1ULL);
v___x_2549_ = lean_usize_add(v_i_2537_, v___x_2548_);
v_i_2537_ = v___x_2549_;
v_b_2538_ = v___x_2547_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2533_ = stack[0].m_obj;
uint8_t v___x_2534_ = stack[1].m_num;
lean_object* v_as_2535_ = stack[2].m_obj;
size_t v_sz_2536_ = stack[3].m_num;
size_t v_i_2537_ = stack[4].m_num;
lean_object* v_b_2538_ = stack[5].m_obj;
lean_object* v___y_2539_ = stack[6].m_obj;
lean_object* v___y_2540_ = stack[7].m_obj;
lean_object* v_res_2567_;
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_2533_, v___x_2534_, v_as_2535_, v_sz_2536_, v_i_2537_, v_b_2538_, v___y_2539_, v___y_2540_);
stack->m_obj
 = v_res_2567_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14___boxed(lean_object* v___x_2568_, lean_object* v___x_2569_, lean_object* v_as_2570_, lean_object* v_sz_2571_, lean_object* v_i_2572_, lean_object* v_b_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v___x_12680__boxed_2577_; size_t v_sz_boxed_2578_; size_t v_i_boxed_2579_; lean_object* v_res_2580_; 
v___x_12680__boxed_2577_ = lean_unbox(v___x_2569_);
v_sz_boxed_2578_ = lean_unbox_usize(v_sz_2571_);
lean_dec(v_sz_2571_);
v_i_boxed_2579_ = lean_unbox_usize(v_i_2572_);
lean_dec(v_i_2572_);
v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_2568_, v___x_12680__boxed_2577_, v_as_2570_, v_sz_boxed_2578_, v_i_boxed_2579_, v_b_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v_as_2570_);
return v_res_2580_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(lean_object* v___x_2584_, uint8_t v___x_2585_, lean_object* v_as_2586_, size_t v_sz_2587_, size_t v_i_2588_, lean_object* v_b_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_usize_dec_lt(v_i_2588_, v_sz_2587_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
lean_dec_ref(v___x_2584_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_b_2589_);
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; lean_object* v_a_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
lean_dec_ref(v_b_2589_);
v___x_2595_ = lean_box(0);
v_a_2601_ = lean_array_uget_borrowed(v_as_2586_, v_i_2588_);
lean_inc_ref(v___x_2584_);
lean_inc(v_a_2601_);
v___x_2602_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2601_, v___x_2584_);
v___x_2603_ = lean_box(0);
v___x_2604_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2585_, v___x_2602_, v___x_2603_);
v___x_2605_ = l_List_isEmpty___redArg(v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___f_2606_; lean_object* v___x_2607_; 
v___f_2606_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2606_, 0, v___x_2604_);
lean_closure_set(v___f_2606_, 1, v___x_2595_);
v___x_2607_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2606_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_dec_ref_known(v___x_2607_, 1);
goto v___jp_2596_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec_ref(v___x_2584_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
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
lean_dec(v___x_2604_);
goto v___jp_2596_;
}
v___jp_2596_:
{
lean_object* v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; 
v___x_2597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0));
v___x_2598_ = ((size_t)1ULL);
v___x_2599_ = lean_usize_add(v_i_2588_, v___x_2598_);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_2584_, v___x_2585_, v_as_2586_, v_sz_2587_, v___x_2599_, v___x_2597_, v___y_2590_, v___y_2591_);
return v___x_2600_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2584_ = stack[0].m_obj;
uint8_t v___x_2585_ = stack[1].m_num;
lean_object* v_as_2586_ = stack[2].m_obj;
size_t v_sz_2587_ = stack[3].m_num;
size_t v_i_2588_ = stack[4].m_num;
lean_object* v_b_2589_ = stack[5].m_obj;
lean_object* v___y_2590_ = stack[6].m_obj;
lean_object* v___y_2591_ = stack[7].m_obj;
lean_object* v_res_2616_;
v_res_2616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_2584_, v___x_2585_, v_as_2586_, v_sz_2587_, v_i_2588_, v_b_2589_, v___y_2590_, v___y_2591_);
stack->m_obj
 = v_res_2616_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___boxed(lean_object* v___x_2617_, lean_object* v___x_2618_, lean_object* v_as_2619_, lean_object* v_sz_2620_, lean_object* v_i_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
uint8_t v___x_12784__boxed_2626_; size_t v_sz_boxed_2627_; size_t v_i_boxed_2628_; lean_object* v_res_2629_; 
v___x_12784__boxed_2626_ = lean_unbox(v___x_2618_);
v_sz_boxed_2627_ = lean_unbox_usize(v_sz_2620_);
lean_dec(v_sz_2620_);
v_i_boxed_2628_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_res_2629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_2617_, v___x_12784__boxed_2626_, v_as_2619_, v_sz_boxed_2627_, v_i_boxed_2628_, v_b_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v_as_2619_);
return v_res_2629_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(lean_object* v_init_2630_, lean_object* v___x_2631_, uint8_t v___x_2632_, lean_object* v_n_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
if (lean_obj_tag(v_n_2633_) == 0)
{
lean_object* v_cs_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; size_t v_sz_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v_cs_2638_ = lean_ctor_get(v_n_2633_, 0);
v___x_2639_ = lean_box(0);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v_b_2634_);
v_sz_2641_ = lean_array_size(v_cs_2638_);
v___x_2642_ = ((size_t)0ULL);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_2630_, v___x_2631_, v___x_2632_, v_cs_2638_, v_sz_2641_, v___x_2642_, v___x_2640_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2658_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2658_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2658_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_fst_2648_; 
v_fst_2648_ = lean_ctor_get(v_a_2644_, 0);
if (lean_obj_tag(v_fst_2648_) == 0)
{
lean_object* v_snd_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v_snd_2649_ = lean_ctor_get(v_a_2644_, 1);
lean_inc(v_snd_2649_);
lean_dec(v_a_2644_);
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_snd_2649_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2650_);
v___x_2652_ = v___x_2646_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
lean_object* v_val_2654_; lean_object* v___x_2656_; 
lean_inc_ref(v_fst_2648_);
lean_dec(v_a_2644_);
v_val_2654_ = lean_ctor_get(v_fst_2648_, 0);
lean_inc(v_val_2654_);
lean_dec_ref_known(v_fst_2648_, 1);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v_val_2654_);
v___x_2656_ = v___x_2646_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_val_2654_);
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
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_a_2659_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2643_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2643_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v_vs_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; size_t v_sz_2670_; size_t v___x_2671_; lean_object* v___x_2672_; 
v_vs_2667_ = lean_ctor_get(v_n_2633_, 0);
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v_b_2634_);
v_sz_2670_ = lean_array_size(v_vs_2667_);
v___x_2671_ = ((size_t)0ULL);
v___x_2672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_2631_, v___x_2632_, v_vs_2667_, v_sz_2670_, v___x_2671_, v___x_2669_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2687_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2687_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2687_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_fst_2677_; 
v_fst_2677_ = lean_ctor_get(v_a_2673_, 0);
if (lean_obj_tag(v_fst_2677_) == 0)
{
lean_object* v_snd_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v_snd_2678_ = lean_ctor_get(v_a_2673_, 1);
lean_inc(v_snd_2678_);
lean_dec(v_a_2673_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_snd_2678_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2679_);
v___x_2681_ = v___x_2675_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
else
{
lean_object* v_val_2683_; lean_object* v___x_2685_; 
lean_inc_ref(v_fst_2677_);
lean_dec(v_a_2673_);
v_val_2683_ = lean_ctor_get(v_fst_2677_, 0);
lean_inc(v_val_2683_);
lean_dec_ref_known(v_fst_2677_, 1);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v_val_2683_);
v___x_2685_ = v___x_2675_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_val_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_a_2688_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2672_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2672_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2630_ = stack[0].m_obj;
lean_object* v___x_2631_ = stack[1].m_obj;
uint8_t v___x_2632_ = stack[2].m_num;
lean_object* v_n_2633_ = stack[3].m_obj;
lean_object* v_b_2634_ = stack[4].m_obj;
lean_object* v___y_2635_ = stack[5].m_obj;
lean_object* v___y_2636_ = stack[6].m_obj;
lean_object* v_res_2696_;
v_res_2696_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2630_, v___x_2631_, v___x_2632_, v_n_2633_, v_b_2634_, v___y_2635_, v___y_2636_);
stack->m_obj
 = v_res_2696_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(lean_object* v_init_2697_, lean_object* v___x_2698_, uint8_t v___x_2699_, lean_object* v_as_2700_, size_t v_sz_2701_, size_t v_i_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
uint8_t v___x_2707_; 
v___x_2707_ = lean_usize_dec_lt(v_i_2702_, v_sz_2701_);
if (v___x_2707_ == 0)
{
lean_object* v___x_2708_; 
lean_dec_ref(v___x_2698_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_b_2703_);
return v___x_2708_;
}
else
{
lean_object* v_snd_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2743_; 
v_snd_2709_ = lean_ctor_get(v_b_2703_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_b_2703_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v_b_2703_, 0);
lean_dec(v_unused_2744_);
v___x_2711_ = v_b_2703_;
v_isShared_2712_ = v_isSharedCheck_2743_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2709_);
lean_dec(v_b_2703_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2743_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_box(0);
v_a_2714_ = lean_array_uget_borrowed(v_as_2700_, v_i_2702_);
lean_inc(v_snd_2709_);
lean_inc_ref(v___x_2698_);
v___x_2715_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2697_, v___x_2698_, v___x_2699_, v_a_2714_, v_snd_2709_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2734_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2734_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2734_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
if (lean_obj_tag(v_a_2716_) == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
lean_dec_ref(v___x_2698_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_a_2716_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2720_);
v___x_2722_ = v___x_2711_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_snd_2709_);
v___x_2722_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2724_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2722_);
v___x_2724_ = v___x_2718_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; 
lean_del_object(v___x_2718_);
lean_dec(v_snd_2709_);
v_a_2727_ = lean_ctor_get(v_a_2716_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v_a_2716_, 1);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_a_2727_);
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2729_ = v___x_2711_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_a_2727_);
v___x_2729_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
size_t v___x_2730_; size_t v___x_2731_; 
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_add(v_i_2702_, v___x_2730_);
v_i_2702_ = v___x_2731_;
v_b_2703_ = v___x_2729_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_del_object(v___x_2711_);
lean_dec(v_snd_2709_);
lean_dec_ref(v___x_2698_);
v_a_2735_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2715_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2715_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2697_ = stack[0].m_obj;
lean_object* v___x_2698_ = stack[1].m_obj;
uint8_t v___x_2699_ = stack[2].m_num;
lean_object* v_as_2700_ = stack[3].m_obj;
size_t v_sz_2701_ = stack[4].m_num;
size_t v_i_2702_ = stack[5].m_num;
lean_object* v_b_2703_ = stack[6].m_obj;
lean_object* v___y_2704_ = stack[7].m_obj;
lean_object* v___y_2705_ = stack[8].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_2697_, v___x_2698_, v___x_2699_, v_as_2700_, v_sz_2701_, v_i_2702_, v_b_2703_, v___y_2704_, v___y_2705_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11___boxed(lean_object* v_init_2746_, lean_object* v___x_2747_, lean_object* v___x_2748_, lean_object* v_as_2749_, lean_object* v_sz_2750_, lean_object* v_i_2751_, lean_object* v_b_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v___x_12882__boxed_2756_; size_t v_sz_boxed_2757_; size_t v_i_boxed_2758_; lean_object* v_res_2759_; 
v___x_12882__boxed_2756_ = lean_unbox(v___x_2748_);
v_sz_boxed_2757_ = lean_unbox_usize(v_sz_2750_);
lean_dec(v_sz_2750_);
v_i_boxed_2758_ = lean_unbox_usize(v_i_2751_);
lean_dec(v_i_2751_);
v_res_2759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_2746_, v___x_2747_, v___x_12882__boxed_2756_, v_as_2749_, v_sz_boxed_2757_, v_i_boxed_2758_, v_b_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec_ref(v_as_2749_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8___boxed(lean_object* v_init_2760_, lean_object* v___x_2761_, lean_object* v___x_2762_, lean_object* v_n_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v___x_12903__boxed_2768_; lean_object* v_res_2769_; 
v___x_12903__boxed_2768_ = lean_unbox(v___x_2762_);
v_res_2769_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2760_, v___x_2761_, v___x_12903__boxed_2768_, v_n_2763_, v_b_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec_ref(v_n_2763_);
return v_res_2769_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(lean_object* v___x_2770_, uint8_t v___x_2771_, lean_object* v_as_2772_, size_t v_sz_2773_, size_t v_i_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
uint8_t v___x_2779_; 
v___x_2779_ = lean_usize_dec_lt(v_i_2774_, v_sz_2773_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_dec_ref(v___x_2770_);
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_b_2775_);
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; lean_object* v_a_2783_; lean_object* v___x_2788_; lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
lean_dec_ref(v_b_2775_);
v___x_2781_ = lean_box(0);
v___x_2788_ = lean_box(0);
v_a_2789_ = lean_array_uget_borrowed(v_as_2772_, v_i_2774_);
lean_inc_ref(v___x_2770_);
lean_inc(v_a_2789_);
v___x_2790_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2789_, v___x_2770_);
v___x_2791_ = lean_box(0);
v___x_2792_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2771_, v___x_2790_, v___x_2791_);
v___x_2793_ = l_List_isEmpty___redArg(v___x_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___f_2794_; lean_object* v___x_2795_; 
v___f_2794_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2794_, 0, v___x_2792_);
lean_closure_set(v___f_2794_, 1, v___x_2788_);
v___x_2795_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2794_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref_known(v___x_2795_, 1);
v_a_2783_ = v___x_2788_;
goto v___jp_2782_;
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v___x_2770_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_dec(v___x_2792_);
v_a_2783_ = v___x_2788_;
goto v___jp_2782_;
}
v___jp_2782_:
{
lean_object* v___x_2784_; size_t v___x_2785_; size_t v___x_2786_; 
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2781_);
lean_ctor_set(v___x_2784_, 1, v_a_2783_);
v___x_2785_ = ((size_t)1ULL);
v___x_2786_ = lean_usize_add(v_i_2774_, v___x_2785_);
v_i_2774_ = v___x_2786_;
v_b_2775_ = v___x_2784_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2770_ = stack[0].m_obj;
uint8_t v___x_2771_ = stack[1].m_num;
lean_object* v_as_2772_ = stack[2].m_obj;
size_t v_sz_2773_ = stack[3].m_num;
size_t v_i_2774_ = stack[4].m_num;
lean_object* v_b_2775_ = stack[5].m_obj;
lean_object* v___y_2776_ = stack[6].m_obj;
lean_object* v___y_2777_ = stack[7].m_obj;
lean_object* v_res_2804_;
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_2770_, v___x_2771_, v_as_2772_, v_sz_2773_, v_i_2774_, v_b_2775_, v___y_2776_, v___y_2777_);
stack->m_obj
 = v_res_2804_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14___boxed(lean_object* v___x_2805_, lean_object* v___x_2806_, lean_object* v_as_2807_, lean_object* v_sz_2808_, lean_object* v_i_2809_, lean_object* v_b_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v___x_13197__boxed_2814_; size_t v_sz_boxed_2815_; size_t v_i_boxed_2816_; lean_object* v_res_2817_; 
v___x_13197__boxed_2814_ = lean_unbox(v___x_2806_);
v_sz_boxed_2815_ = lean_unbox_usize(v_sz_2808_);
lean_dec(v_sz_2808_);
v_i_boxed_2816_ = lean_unbox_usize(v_i_2809_);
lean_dec(v_i_2809_);
v_res_2817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_2805_, v___x_13197__boxed_2814_, v_as_2807_, v_sz_boxed_2815_, v_i_boxed_2816_, v_b_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v_as_2807_);
return v_res_2817_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(lean_object* v___x_2821_, uint8_t v___x_2822_, lean_object* v_as_2823_, size_t v_sz_2824_, size_t v_i_2825_, lean_object* v_b_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v___x_2830_; 
v___x_2830_ = lean_usize_dec_lt(v_i_2825_, v_sz_2824_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
lean_dec_ref(v___x_2821_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_b_2826_);
return v___x_2831_;
}
else
{
lean_object* v___x_2832_; lean_object* v_a_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; 
lean_dec_ref(v_b_2826_);
v___x_2832_ = lean_box(0);
v_a_2838_ = lean_array_uget_borrowed(v_as_2823_, v_i_2825_);
lean_inc_ref(v___x_2821_);
lean_inc(v_a_2838_);
v___x_2839_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_2838_, v___x_2821_);
v___x_2840_ = lean_box(0);
v___x_2841_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_2822_, v___x_2839_, v___x_2840_);
v___x_2842_ = l_List_isEmpty___redArg(v___x_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___f_2843_; lean_object* v___x_2844_; 
v___f_2843_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2843_, 0, v___x_2841_);
lean_closure_set(v___f_2843_, 1, v___x_2832_);
v___x_2844_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2843_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_dec_ref_known(v___x_2844_, 1);
goto v___jp_2833_;
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref(v___x_2821_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_dec(v___x_2841_);
goto v___jp_2833_;
}
v___jp_2833_:
{
lean_object* v___x_2834_; size_t v___x_2835_; size_t v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0));
v___x_2835_ = ((size_t)1ULL);
v___x_2836_ = lean_usize_add(v_i_2825_, v___x_2835_);
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_2821_, v___x_2822_, v_as_2823_, v_sz_2824_, v___x_2836_, v___x_2834_, v___y_2827_, v___y_2828_);
return v___x_2837_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2821_ = stack[0].m_obj;
uint8_t v___x_2822_ = stack[1].m_num;
lean_object* v_as_2823_ = stack[2].m_obj;
size_t v_sz_2824_ = stack[3].m_num;
size_t v_i_2825_ = stack[4].m_num;
lean_object* v_b_2826_ = stack[5].m_obj;
lean_object* v___y_2827_ = stack[6].m_obj;
lean_object* v___y_2828_ = stack[7].m_obj;
lean_object* v_res_2853_;
v_res_2853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_2821_, v___x_2822_, v_as_2823_, v_sz_2824_, v_i_2825_, v_b_2826_, v___y_2827_, v___y_2828_);
stack->m_obj
 = v_res_2853_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___boxed(lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v_as_2856_, lean_object* v_sz_2857_, lean_object* v_i_2858_, lean_object* v_b_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v___x_13301__boxed_2863_; size_t v_sz_boxed_2864_; size_t v_i_boxed_2865_; lean_object* v_res_2866_; 
v___x_13301__boxed_2863_ = lean_unbox(v___x_2855_);
v_sz_boxed_2864_ = lean_unbox_usize(v_sz_2857_);
lean_dec(v_sz_2857_);
v_i_boxed_2865_ = lean_unbox_usize(v_i_2858_);
lean_dec(v_i_2858_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_2854_, v___x_13301__boxed_2863_, v_as_2856_, v_sz_boxed_2864_, v_i_boxed_2865_, v_b_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v_as_2856_);
return v_res_2866_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(lean_object* v___x_2867_, uint8_t v___x_2868_, lean_object* v_t_2869_, lean_object* v_init_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_root_2874_; lean_object* v_tail_2875_; lean_object* v___x_2876_; 
v_root_2874_ = lean_ctor_get(v_t_2869_, 0);
v_tail_2875_ = lean_ctor_get(v_t_2869_, 1);
lean_inc_ref(v___x_2867_);
v___x_2876_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_2870_, v___x_2867_, v___x_2868_, v_root_2874_, v_init_2870_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2913_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_2913_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2913_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
if (lean_obj_tag(v_a_2877_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2883_; 
lean_dec_ref(v___x_2867_);
v_a_2881_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v_a_2877_, 1);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v_a_2881_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; size_t v_sz_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
lean_del_object(v___x_2879_);
v_a_2885_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v_a_2877_, 1);
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v_a_2885_);
v_sz_2888_ = lean_array_size(v_tail_2875_);
v___x_2889_ = ((size_t)0ULL);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_2867_, v___x_2868_, v_tail_2875_, v_sz_2888_, v___x_2889_, v___x_2887_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2904_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2904_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2904_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v_fst_2895_; 
v_fst_2895_ = lean_ctor_get(v_a_2891_, 0);
if (lean_obj_tag(v_fst_2895_) == 0)
{
lean_object* v_snd_2896_; lean_object* v___x_2898_; 
v_snd_2896_ = lean_ctor_get(v_a_2891_, 1);
lean_inc(v_snd_2896_);
lean_dec(v_a_2891_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v_snd_2896_);
v___x_2898_ = v___x_2893_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_snd_2896_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
else
{
lean_object* v_val_2900_; lean_object* v___x_2902_; 
lean_inc_ref(v_fst_2895_);
lean_dec(v_a_2891_);
v_val_2900_ = lean_ctor_get(v_fst_2895_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v_fst_2895_, 1);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v_val_2900_);
v___x_2902_ = v___x_2893_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_val_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
v_a_2905_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2890_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2890_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___x_2867_);
v_a_2914_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2876_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2876_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2867_ = stack[0].m_obj;
uint8_t v___x_2868_ = stack[1].m_num;
lean_object* v_t_2869_ = stack[2].m_obj;
lean_object* v_init_2870_ = stack[3].m_obj;
lean_object* v___y_2871_ = stack[4].m_obj;
lean_object* v___y_2872_ = stack[5].m_obj;
lean_object* v_res_2922_;
v_res_2922_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v___x_2867_, v___x_2868_, v_t_2869_, v_init_2870_, v___y_2871_, v___y_2872_);
stack->m_obj
 = v_res_2922_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5___boxed(lean_object* v___x_2923_, lean_object* v___x_2924_, lean_object* v_t_2925_, lean_object* v_init_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
uint8_t v___x_13399__boxed_2930_; lean_object* v_res_2931_; 
v___x_13399__boxed_2930_ = lean_unbox(v___x_2924_);
v_res_2931_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v___x_2923_, v___x_13399__boxed_2930_, v_t_2925_, v_init_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_t_2925_);
return v_res_2931_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(lean_object* v_o_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v_env_2937_; lean_object* v___x_2938_; lean_object* v_toEnvExtension_2939_; lean_object* v_asyncMode_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; lean_object* v_merged_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2952_; 
v___x_2935_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2936_ = lean_st_ref_get(v___y_2933_);
v_env_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc_ref(v_env_2937_);
lean_dec(v___x_2936_);
v___x_2938_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2939_ = lean_ctor_get(v___x_2938_, 0);
v_asyncMode_2940_ = lean_ctor_get(v_toEnvExtension_2939_, 2);
v___x_2941_ = lean_box(0);
v___x_2942_ = 0;
v___x_2943_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2935_, v___x_2938_, v_env_2937_, v_asyncMode_2940_, v___x_2941_, v___x_2942_);
v_merged_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2952_ == 0)
{
lean_object* v_unused_2953_; 
v_unused_2953_ = lean_ctor_get(v___x_2943_, 1);
lean_dec(v_unused_2953_);
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_merged_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2952_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 1, v_merged_2944_);
lean_ctor_set(v___x_2946_, 0, v_o_2932_);
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_o_2932_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_merged_2944_);
v___x_2949_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2932_ = stack[0].m_obj;
lean_object* v___y_2933_ = stack[1].m_obj;
lean_object* v_res_2954_;
v_res_2954_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_2932_, v___y_2933_);
stack->m_obj
 = v_res_2954_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_2955_, v___y_2956_);
lean_dec(v___y_2956_);
return v_res_2958_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v_scopes_2964_; lean_object* v___x_2965_; lean_object* v_opts_2966_; lean_object* v___x_2967_; 
v___x_2962_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2963_ = lean_st_ref_get(v___y_2960_);
v_scopes_2964_ = lean_ctor_get(v___x_2963_, 2);
lean_inc(v_scopes_2964_);
lean_dec(v___x_2963_);
v___x_2965_ = l_List_head_x21___redArg(v___x_2962_, v_scopes_2964_);
lean_dec(v_scopes_2964_);
v_opts_2966_ = lean_ctor_get(v___x_2965_, 1);
lean_inc_ref(v_opts_2966_);
lean_dec(v___x_2965_);
v___x_2967_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_opts_2966_, v___y_2960_);
return v___x_2967_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2959_ = stack[0].m_obj;
lean_object* v___y_2960_ = stack[1].m_obj;
lean_object* v_res_2968_;
v_res_2968_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_2959_, v___y_2960_);
stack->m_obj
 = v_res_2968_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0___boxed(lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2972_;
}
}
lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(lean_object* v_x_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3014_; 
v___x_2977_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_2974_, v___y_2975_);
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_3014_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3014_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; uint8_t v___y_2984_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_2982_ = lean_st_ref_get(v___y_2975_);
v___x_3010_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
v___x_3011_ = l_Lean_Linter_getLinterValue(v___x_3010_, v_a_2978_);
lean_dec(v_a_2978_);
if (v___x_3011_ == 0)
{
lean_dec(v___x_2982_);
v___y_2984_ = v___x_3011_;
goto v___jp_2983_;
}
else
{
lean_object* v_infoState_3012_; uint8_t v_enabled_3013_; 
v_infoState_3012_ = lean_ctor_get(v___x_2982_, 8);
lean_inc_ref(v_infoState_3012_);
lean_dec(v___x_2982_);
v_enabled_3013_ = lean_ctor_get_uint8(v_infoState_3012_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3012_);
v___y_2984_ = v_enabled_3013_;
goto v___jp_2983_;
}
v___jp_2983_:
{
if (v___y_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_box(0);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_2985_);
v___x_2987_ = v___x_2980_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
else
{
lean_object* v___x_2989_; lean_object* v_messages_2990_; uint8_t v___x_2991_; 
v___x_2989_ = lean_st_ref_get(v___y_2975_);
v_messages_2990_ = lean_ctor_get(v___x_2989_, 1);
lean_inc_ref(v_messages_2990_);
lean_dec(v___x_2989_);
v___x_2991_ = l_Lean_MessageLog_hasErrors(v_messages_2990_);
lean_dec_ref(v_messages_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v_env_2993_; lean_object* v___x_2994_; lean_object* v_a_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_del_object(v___x_2980_);
v___x_2992_ = lean_st_ref_get(v___y_2975_);
v_env_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc_ref(v_env_2993_);
lean_dec(v___x_2992_);
v___x_2994_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_2975_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = lean_box(0);
v___x_2997_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v_env_2993_, v___x_2991_, v_a_2995_, v___x_2996_, v___y_2974_, v___y_2975_);
lean_dec(v_a_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v___x_2997_, 0);
lean_dec(v_unused_3005_);
v___x_2999_ = v___x_2997_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_dec(v___x_2997_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_2996_);
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2996_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
else
{
return v___x_2997_;
}
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3006_ = lean_box(0);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_3006_);
v___x_3008_ = v___x_2980_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2973_ = stack[0].m_obj;
lean_object* v___y_2974_ = stack[1].m_obj;
lean_object* v___y_2975_ = stack[2].m_obj;
lean_object* v_res_3015_;
v_res_3015_ = l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(v_x_2973_, v___y_2974_, v___y_2975_);
stack->m_obj
 = v_res_3015_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0___boxed(lean_object* v_x_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(v_x_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v_x_3016_);
return v_res_3020_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(lean_object* v_o_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_3036_, v___y_3038_);
return v___x_3040_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_3036_ = stack[0].m_obj;
lean_object* v___y_3037_ = stack[1].m_obj;
lean_object* v___y_3038_ = stack[2].m_obj;
lean_object* v_res_3041_;
v_res_3041_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(v_o_3036_, v___y_3037_, v___y_3038_);
stack->m_obj
 = v_res_3041_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___boxed(lean_object* v_o_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(v_o_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3046_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(lean_object* v_as_3047_, lean_object* v_as_x27_3048_, lean_object* v_b_3049_, lean_object* v_a_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_3048_, v_b_3049_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3047_ = stack[0].m_obj;
lean_object* v_as_x27_3048_ = stack[1].m_obj;
lean_object* v_b_3049_ = stack[2].m_obj;
lean_object* v___y_3051_ = stack[4].m_obj;
lean_object* v___y_3052_ = stack[5].m_obj;
lean_object* v___y_3053_ = stack[6].m_obj;
lean_object* v___y_3054_ = stack[7].m_obj;
lean_object* v___y_3055_ = stack[8].m_obj;
lean_object* v___y_3056_ = stack[9].m_obj;
lean_object* v_res_3059_;
v_res_3059_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(v_as_3047_, v_as_x27_3048_, v_b_3049_, lean_box(0), v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
stack->m_obj
 = v_res_3059_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___boxed(lean_object* v_as_3060_, lean_object* v_as_x27_3061_, lean_object* v_b_3062_, lean_object* v_a_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(v_as_3060_, v_as_x27_3061_, v_b_3062_, v_a_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v_as_x27_3061_);
lean_dec(v_as_3060_);
return v_res_3071_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(lean_object* v_o_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___redArg(v_o_3072_, v___y_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_3072_ = stack[0].m_obj;
lean_object* v___y_3073_ = stack[1].m_obj;
lean_object* v___y_3074_ = stack[2].m_obj;
lean_object* v___y_3075_ = stack[3].m_obj;
lean_object* v___y_3076_ = stack[4].m_obj;
lean_object* v___y_3077_ = stack[5].m_obj;
lean_object* v___y_3078_ = stack[6].m_obj;
lean_object* v_res_3081_;
v_res_3081_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(v_o_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
stack->m_obj
 = v_res_3081_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_o_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__3_spec__4(v_o_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3090_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(lean_object* v_ref_3091_, lean_object* v_msgData_3092_, uint8_t v_severity_3093_, uint8_t v_isSilent_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___redArg(v_ref_3091_, v_msgData_3092_, v_severity_3093_, v_isSilent_3094_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
return v___x_3102_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3091_ = stack[0].m_obj;
lean_object* v_msgData_3092_ = stack[1].m_obj;
uint8_t v_severity_3093_ = stack[2].m_num;
uint8_t v_isSilent_3094_ = stack[3].m_num;
lean_object* v___y_3095_ = stack[4].m_obj;
lean_object* v___y_3096_ = stack[5].m_obj;
lean_object* v___y_3097_ = stack[6].m_obj;
lean_object* v___y_3098_ = stack[7].m_obj;
lean_object* v___y_3099_ = stack[8].m_obj;
lean_object* v___y_3100_ = stack[9].m_obj;
lean_object* v_res_3103_;
v_res_3103_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(v_ref_3091_, v_msgData_3092_, v_severity_3093_, v_isSilent_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
stack->m_obj
 = v_res_3103_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10___boxed(lean_object* v_ref_3104_, lean_object* v_msgData_3105_, lean_object* v_severity_3106_, lean_object* v_isSilent_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
uint8_t v_severity_boxed_3115_; uint8_t v_isSilent_boxed_3116_; lean_object* v_res_3117_; 
v_severity_boxed_3115_ = lean_unbox(v_severity_3106_);
v_isSilent_boxed_3116_ = lean_unbox(v_isSilent_3107_);
v_res_3117_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2_spec__4_spec__6_spec__10(v_ref_3104_, v_msgData_3105_, v_severity_boxed_3115_, v_isSilent_boxed_3116_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v_ref_3104_);
return v_res_3117_;
}
}
lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter));
v___x_3120_ = l_Lean_Elab_Command_addLinter(v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3121_;
v_res_3121_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3121_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2____boxed(lean_object* v_a_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
return v_res_3123_;
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
