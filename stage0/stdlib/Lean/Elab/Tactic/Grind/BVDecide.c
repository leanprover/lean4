// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.BVDecide
// Imports: import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Tactic.BVDecide.Main import Lean.Elab.Tactic.BVDecide import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Tactic.Grind.BVDecide.Types
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
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_remove_file(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 16, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bvDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__4_value),LEAN_SCALAR_PTR_LITERAL(184, 150, 103, 35, 70, 25, 10, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6_value),LEAN_SCALAR_PTR_LITERAL(33, 50, 202, 5, 86, 233, 189, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__8_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTypes"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__10_value),LEAN_SCALAR_PTR_LITERAL(133, 159, 97, 61, 240, 205, 127, 31)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(246, 172, 74, 48, 93, 132, 233, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(159, 125, 89, 202, 91, 47, 27, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 43, 102, 233, 206, 49, 244, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(48, 28, 174, 40, 141, 254, 11, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 205, 242, 16, 234, 190, 33, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 17, 49, 200, 191, 147, 94, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalBvDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(245, 19, 110, 32, 0, 147, 105, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindStep"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 239, 5, 217, 230, 199, 187, 87)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "grindSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "haveSilent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 40, 33, 99, 54, 221, 176, 65)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value_aux_3),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(148, 36, 229, 233, 71, 216, 202, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__15_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(178, 14, 254, 151, 151, 84, 196, 42)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__18_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__16_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__20_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__25_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 142, 92, 236, 193, 5, 157, 115)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "bv_decide\?"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__4_value),LEAN_SCALAR_PTR_LITERAL(89, 224, 172, 67, 205, 21, 228, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "bvNormalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6_value),LEAN_SCALAR_PTR_LITERAL(42, 26, 136, 123, 235, 182, 158, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__10_value),LEAN_SCALAR_PTR_LITERAL(39, 89, 115, 113, 62, 113, 141, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_check"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvTrace"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 31, 96, 242, 225, 204, 89, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12_value),LEAN_SCALAR_PTR_LITERAL(150, 149, 7, 180, 70, 199, 193, 180)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "evalBvCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 159, 63, 127, 180, 167, 31, 248)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8_value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`bv_normalize` failed to close the goal"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalBVNormalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 164, 205, 143, 231, 178, 56, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___boxed(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Elab.Tactic.Grind.BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "_private.Lean.Elab.Tactic.Grind.BVDecide.0.Lean.Elab.Tactic.Grind.evalBVPush"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bvDecidePush"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 198, 224, 172, 164, 17, 35, 6)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "bv_decide_push"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 213, 41, 102, 56, 1, 176, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalBVPush"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 92, 190, 201, 240, 246, 88, 127)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(lean_object* v_cfg_9_, lean_object* v_goal_10_, lean_object* v_elaborator_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_15_ = 1;
v___x_16_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0));
v___x_17_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_17_, 0, v_elaborator_11_);
lean_ctor_set_uint8(v___x_17_, sizeof(void*)*1, v___x_15_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v_goal_10_);
lean_ctor_set(v___x_19_, 1, v___x_18_);
v___x_20_ = lean_st_mk_ref(v___x_19_);
v___x_21_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_9_, v___x_16_, v___x_15_, v___x_17_, v_a_12_, v_a_13_);
lean_dec_ref_known(v___x_17_, 1);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_30_ == 0)
{
v___x_24_ = v___x_21_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_26_ = lean_st_ref_get(v___x_20_);
lean_dec(v___x_20_);
lean_dec(v___x_26_);
if (v_isShared_25_ == 0)
{
v___x_28_ = v___x_24_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_22_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_dec(v___x_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_31_, lean_object* v_goal_32_, lean_object* v_elaborator_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_31_, v_goal_32_, v_elaborator_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(lean_object* v_cfg_38_, lean_object* v_goal_39_, lean_object* v_elaborator_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_38_, v_goal_39_, v_elaborator_40_, v_a_45_, v_a_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___boxed(lean_object* v_cfg_49_, lean_object* v_goal_50_, lean_object* v_elaborator_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(v_cfg_49_, v_goal_50_, v_elaborator_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
return v_res_59_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_object* v_00_u03b1_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(v_00_u03b1_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_90_, lean_object* v_ref_91_, lean_object* v_a_x3f_92_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_io_remove_file(v_snd_90_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec(v_ref_91_);
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
v_a_103_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_114_ == 0)
{
v___x_105_ = v___x_94_;
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_94_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_107_ = lean_io_error_to_string(v_a_103_);
v___x_108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
v___x_109_ = l_Lean_MessageData_ofFormat(v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v_ref_91_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_110_);
v___x_112_ = v___x_105_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_115_, lean_object* v_ref_116_, lean_object* v_a_x3f_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_115_, v_ref_116_, v_a_x3f_117_);
lean_dec(v_a_x3f_117_);
lean_dec_ref(v_snd_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(lean_object* v_f_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_ref_130_; lean_object* v___x_131_; 
v_ref_130_ = lean_ctor_get(v___y_127_, 2);
v___x_131_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v_fst_133_; lean_object* v_snd_134_; lean_object* v_r_135_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 1);
v_fst_133_ = lean_ctor_get(v_a_132_, 0);
lean_inc(v_fst_133_);
v_snd_134_ = lean_ctor_get(v_a_132_, 1);
lean_inc_n(v_snd_134_, 2);
lean_dec(v_a_132_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
lean_inc(v___y_124_);
lean_inc_ref(v___y_123_);
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
v_r_135_ = lean_apply_11(v_f_120_, v_fst_133_, v_snd_134_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
if (lean_obj_tag(v_r_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_160_; 
v_a_136_ = lean_ctor_get(v_r_135_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_r_135_);
if (v_isSharedCheck_160_ == 0)
{
v___x_138_ = v_r_135_;
v_isShared_139_ = v_isSharedCheck_160_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v_r_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_160_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
lean_inc(v_a_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 1);
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_159_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
lean_inc(v_ref_130_);
v___x_142_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_134_, v_ref_130_, v___x_141_);
lean_dec_ref(v___x_141_);
lean_dec(v_snd_134_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v___x_142_, 0);
lean_dec(v_unused_150_);
v___x_144_ = v___x_142_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_dec(v___x_142_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v_a_136_);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_136_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_a_136_);
v_a_151_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_142_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_142_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_161_ = lean_ctor_get(v_r_135_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v_r_135_, 1);
v___x_162_ = lean_box(0);
lean_inc(v_ref_130_);
v___x_163_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_134_, v_ref_130_, v___x_162_);
lean_dec(v_snd_134_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; 
v_unused_171_ = lean_ctor_get(v___x_163_, 0);
lean_dec(v_unused_171_);
v___x_165_ = v___x_163_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_dec(v___x_163_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 1);
lean_ctor_set(v___x_165_, 0, v_a_161_);
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_161_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_a_161_);
v_a_172_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_163_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_163_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_191_; 
lean_dec_ref(v_f_120_);
v_a_180_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_191_ == 0)
{
v___x_182_ = v___x_131_;
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_131_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_191_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_184_ = lean_io_error_to_string(v_a_180_);
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
v___x_186_ = l_Lean_MessageData_ofFormat(v___x_185_);
lean_inc(v_ref_130_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_ref_130_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_187_);
v___x_189_ = v___x_182_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(lean_object* v_00_u03b1_203_, lean_object* v_f_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_215_, lean_object* v_f_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(v_00_u03b1_215_, v_f_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_x_230_, lean_object* v_lratFile_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_231_, v_a_227_, v_a_228_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_241_, 1);
v___x_243_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_243_, 0, v_a_229_);
v___x_244_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_244_, 0, v___x_243_);
lean_closure_set(v___x_244_, 1, v_a_242_);
v___x_245_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_244_, v___y_232_, v___y_233_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref_known(v___x_245_, 1);
v___x_246_ = lean_box(0);
v___x_247_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_246_, v___y_233_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v___x_247_;
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
v_a_248_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_245_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_a_229_);
v_a_256_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_241_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_241_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed(lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_x_267_, lean_object* v_lratFile_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(v_a_264_, v_a_265_, v_a_266_, v_x_267_, v_lratFile_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v_x_267_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
lean_inc(v_x_305_);
v___x_316_ = l_Lean_Syntax_isOfKind(v_x_305_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec(v_x_305_);
v___x_317_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v_cfg_319_; lean_object* v_types_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v_cfg_319_ = l_Lean_Syntax_getArg(v_x_305_, v___x_318_);
v___x_365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_319_);
v___x_366_ = l_Lean_Syntax_isOfKind(v_cfg_319_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v_cfg_319_);
lean_dec(v_x_305_);
v___x_367_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = lean_unsigned_to_nat(2u);
v___x_369_ = l_Lean_Syntax_getArg(v_x_305_, v___x_368_);
lean_dec(v_x_305_);
v___x_370_ = l_Lean_Syntax_isNone(v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
lean_inc(v___x_369_);
v___x_371_ = l_Lean_Syntax_matchesNull(v___x_369_, v___x_318_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec(v___x_369_);
lean_dec(v_cfg_319_);
v___x_372_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v_types_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_unsigned_to_nat(0u);
v_types_374_ = l_Lean_Syntax_getArg(v___x_369_, v___x_373_);
lean_dec(v___x_369_);
v___x_375_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_374_);
v___x_376_ = l_Lean_Syntax_isOfKind(v_types_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_types_374_);
lean_dec(v_cfg_319_);
v___x_377_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_377_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v_types_374_);
v_types_321_ = v___x_378_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_307_;
v___y_324_ = v_a_308_;
v___y_325_ = v_a_309_;
v___y_326_ = v_a_310_;
v___y_327_ = v_a_311_;
v___y_328_ = v_a_312_;
v___y_329_ = v_a_313_;
goto v___jp_320_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_369_);
v___x_379_ = lean_box(0);
v_types_321_ = v___x_379_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_307_;
v___y_324_ = v_a_308_;
v___y_325_ = v_a_309_;
v___y_326_ = v_a_310_;
v___y_327_ = v_a_311_;
v___y_328_ = v_a_312_;
v___y_329_ = v_a_313_;
goto v___jp_320_;
}
}
v___jp_320_:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; 
lean_dec_ref_known(v___x_330_, 1);
v___x_331_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_323_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_mvarId_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v_mvarId_333_ = lean_ctor_get(v_a_332_, 1);
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7));
lean_inc(v_mvarId_333_);
v___x_335_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_319_, v_mvarId_333_, v___x_334_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_321_, v_a_336_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___f_339_; lean_object* v___x_340_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___f_339_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed), 14, 3);
lean_closure_set(v___f_339_, 0, v_a_336_);
lean_closure_set(v___f_339_, 1, v_a_338_);
lean_closure_set(v___f_339_, 2, v_a_332_);
v___x_340_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v___f_339_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_340_;
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_a_336_);
lean_dec(v_a_332_);
v_a_341_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_337_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_337_);
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
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_a_332_);
lean_dec(v_types_321_);
v_a_349_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_335_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_335_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_types_321_);
lean_dec(v_cfg_319_);
v_a_357_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_331_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_331_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_dec(v_types_321_);
lean_dec(v_cfg_319_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(v_x_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1(){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_432_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15));
v___x_435_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed), 10, 0);
v___x_436_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_432_, v___x_433_, v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___boxed(lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
lean_inc(v___y_441_);
lean_inc_ref(v___y_440_);
v___x_449_ = lean_apply_9(v_x_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_461_, lean_object* v_x_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___f_472_; lean_object* v___x_473_; 
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
v___f_472_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_472_, 0, v_x_462_);
lean_closure_set(v___f_472_, 1, v___y_463_);
lean_closure_set(v___f_472_, 2, v___y_464_);
lean_closure_set(v___f_472_, 3, v___y_465_);
lean_closure_set(v___f_472_, 4, v___y_466_);
v___x_473_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_461_, v___f_472_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_473_) == 0)
{
return v___x_473_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(lean_object* v_00_u03b1_494_, lean_object* v_mvarId_495_, lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_495_, v_x_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_507_, lean_object* v_mvarId_508_, lean_object* v_x_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(v_00_u03b1_507_, v_mvarId_508_, v_x_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_519_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Array_mkArray0___redArg();
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(size_t v_sz_531_, size_t v_i_532_, lean_object* v_bs_533_, lean_object* v___y_534_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = lean_usize_dec_lt(v_i_532_, v_sz_531_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_bs_533_);
return v___x_537_;
}
else
{
lean_object* v_ref_538_; lean_object* v_v_539_; lean_object* v___x_540_; lean_object* v_bs_x27_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v_ref_538_ = lean_ctor_get(v___y_534_, 2);
v_v_539_ = lean_array_uget(v_bs_533_, v_i_532_);
v___x_540_ = lean_unsigned_to_nat(0u);
v_bs_x27_541_ = lean_array_uset(v_bs_533_, v_i_532_, v___x_540_);
v___x_542_ = 0;
v___x_543_ = l_Lean_SourceInfo_fromRef(v_ref_538_, v___x_542_);
v___x_544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1));
v___x_545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
lean_inc(v___x_543_);
v___x_547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_547_, 0, v___x_543_);
lean_ctor_set(v___x_547_, 1, v___x_545_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
v___x_548_ = l_Lean_Syntax_node2(v___x_543_, v___x_544_, v_v_539_, v___x_547_);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_532_, v___x_549_);
v___x_551_ = lean_array_uset(v_bs_x27_541_, v_i_532_, v___x_548_);
v_i_532_ = v___x_550_;
v_bs_533_ = v___x_551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___boxed(lean_object* v_sz_553_, lean_object* v_i_554_, lean_object* v_bs_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_553_);
lean_dec(v_sz_553_);
v_i_boxed_559_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_boxed_558_, v_i_boxed_559_, v_bs_555_, v___y_556_);
lean_dec_ref(v___y_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(lean_object* v_a_564_, size_t v___x_565_, lean_object* v___x_566_, lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v___x_569_, lean_object* v_final_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; size_t v_sz_577_; lean_object* v___x_578_; 
v___x_576_ = lean_array_push(v_a_564_, v_final_570_);
v_sz_577_ = lean_array_size(v___x_576_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_577_, v___x_565_, v___x_576_, v___y_573_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_601_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_601_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_601_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_ref_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v_ref_583_ = lean_ctor_get(v___y_573_, 2);
v___x_584_ = 0;
v___x_585_ = l_Lean_SourceInfo_fromRef(v_ref_583_, v___x_584_);
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0));
lean_inc_ref(v___x_569_);
lean_inc_ref(v___x_568_);
lean_inc_ref(v___x_567_);
lean_inc_ref(v___x_566_);
v___x_587_ = l_Lean_Name_mkStr5(v___x_566_, v___x_567_, v___x_568_, v___x_569_, v___x_586_);
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1));
v___x_589_ = l_Lean_Name_mkStr5(v___x_566_, v___x_567_, v___x_568_, v___x_569_, v___x_588_);
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_591_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
v___x_593_ = l_Lean_Syntax_SepArray_ofElems(v___x_592_, v_a_579_);
lean_dec(v_a_579_);
v___x_594_ = l_Array_append___redArg(v___x_591_, v___x_593_);
lean_dec_ref(v___x_593_);
lean_inc_n(v___x_585_, 2);
v___x_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_585_);
lean_ctor_set(v___x_595_, 1, v___x_590_);
lean_ctor_set(v___x_595_, 2, v___x_594_);
v___x_596_ = l_Lean_Syntax_node1(v___x_585_, v___x_589_, v___x_595_);
v___x_597_ = l_Lean_Syntax_node1(v___x_585_, v___x_587_, v___x_596_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_597_);
v___x_599_ = v___x_581_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v___x_569_);
lean_dec_ref(v___x_568_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v___x_566_);
v_a_602_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_578_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_578_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed(lean_object* v_a_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v_final_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
size_t v___x_26600__boxed_622_; lean_object* v_res_623_; 
v___x_26600__boxed_622_ = lean_unbox_usize(v___x_611_);
lean_dec(v___x_611_);
v_res_623_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(v_a_610_, v___x_26600__boxed_622_, v___x_612_, v___x_613_, v___x_614_, v___x_615_, v_final_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_623_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
v___x_662_ = l_String_toRawSubstring_x27(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(size_t v_sz_698_, size_t v_i_699_, lean_object* v_bs_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_bs_700_);
return v___x_707_;
}
else
{
lean_object* v_v_708_; lean_object* v_hyp_709_; lean_object* v_grindProof_710_; lean_object* v_type_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_796_; 
v_v_708_ = lean_array_uget_borrowed(v_bs_700_, v_i_699_);
v_hyp_709_ = lean_ctor_get(v_v_708_, 0);
lean_inc_ref(v_hyp_709_);
v_grindProof_710_ = lean_ctor_get(v_v_708_, 2);
lean_inc_ref(v_grindProof_710_);
v_type_711_ = lean_ctor_get(v_hyp_709_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_hyp_709_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; lean_object* v_unused_798_; lean_object* v_unused_799_; 
v_unused_797_ = lean_ctor_get(v_hyp_709_, 3);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_hyp_709_, 2);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_hyp_709_, 0);
lean_dec(v_unused_799_);
v___x_713_ = v_hyp_709_;
v_isShared_714_ = v_isSharedCheck_796_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_type_711_);
lean_dec(v_hyp_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_796_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v_bs_x27_716_; lean_object* v_a_718_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_715_ = lean_unsigned_to_nat(0u);
v_bs_x27_716_ = lean_array_uset(v_bs_700_, v_i_699_, v___x_715_);
v___x_723_ = lean_box(1);
v___x_724_ = l_Lean_PrettyPrinter_delab(v_type_711_, v___x_723_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
v___x_726_ = lean_apply_5(v_grindProof_710_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, lean_box(0));
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
if (lean_obj_tag(v_a_727_) == 0)
{
lean_object* v_ref_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
lean_del_object(v___x_713_);
v_ref_728_ = lean_ctor_get(v___y_703_, 2);
v___x_729_ = 0;
v___x_730_ = l_Lean_SourceInfo_fromRef(v_ref_728_, v___x_729_);
v___x_731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1));
v___x_732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
lean_inc_n(v___x_730_, 3);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_730_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
v___x_736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_736_, 0, v___x_730_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
v___x_738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_730_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_Syntax_node4(v___x_730_, v___x_731_, v___x_733_, v___x_736_, v___x_738_, v_a_725_);
v_a_718_ = v___x_739_;
goto v___jp_717_;
}
else
{
lean_object* v_toCold_740_; lean_object* v_val_741_; lean_object* v_ref_742_; lean_object* v_quotContext_743_; lean_object* v_currMacroScope_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v_toCold_740_ = lean_ctor_get(v___y_703_, 0);
v_val_741_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v_a_727_, 1);
v_ref_742_ = lean_ctor_get(v___y_703_, 2);
v_quotContext_743_ = lean_ctor_get(v_toCold_740_, 8);
v_currMacroScope_744_ = lean_ctor_get(v_toCold_740_, 9);
v___x_745_ = 0;
v___x_746_ = l_Lean_SourceInfo_fromRef(v_ref_742_, v___x_745_);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4));
lean_inc_n(v___x_746_, 2);
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_746_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7));
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9));
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11));
v___x_753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13));
v___x_754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14);
v___x_755_ = lean_box(0);
lean_inc(v_currMacroScope_744_);
lean_inc(v_quotContext_743_);
v___x_756_ = l_Lean_addMacroScope(v_quotContext_743_, v___x_755_, v_currMacroScope_744_);
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21));
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 3);
lean_ctor_set(v___x_713_, 3, v___x_757_);
lean_ctor_set(v___x_713_, 2, v___x_756_);
lean_ctor_set(v___x_713_, 1, v___x_754_);
lean_ctor_set(v___x_713_, 0, v___x_746_);
v___x_759_ = v___x_713_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v___x_757_);
v___x_759_ = v_reuseFailAlloc_779_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_inc_n(v___x_746_, 11);
v___x_760_ = l_Lean_Syntax_node1(v___x_746_, v___x_753_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node1(v___x_746_, v___x_752_, v___x_760_);
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_763_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
v___x_764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_764_, 0, v___x_746_);
lean_ctor_set(v___x_764_, 1, v___x_762_);
lean_ctor_set(v___x_764_, 2, v___x_763_);
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23));
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_746_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_Syntax_node2(v___x_746_, v___x_765_, v___x_767_, v_a_725_);
v___x_769_ = l_Lean_Syntax_node1(v___x_746_, v___x_762_, v___x_768_);
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24));
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_746_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26));
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27));
v___x_774_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_746_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Lean_Syntax_node2(v___x_746_, v___x_772_, v___x_774_, v_val_741_);
v___x_776_ = l_Lean_Syntax_node5(v___x_746_, v___x_751_, v___x_761_, v___x_764_, v___x_769_, v___x_771_, v___x_775_);
v___x_777_ = l_Lean_Syntax_node1(v___x_746_, v___x_750_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node2(v___x_746_, v___x_748_, v___x_749_, v___x_777_);
v_a_718_ = v___x_778_;
goto v___jp_717_;
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v_a_725_);
lean_dec_ref(v_bs_x27_716_);
lean_del_object(v___x_713_);
v_a_780_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_726_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_726_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v_bs_x27_716_);
lean_del_object(v___x_713_);
lean_dec_ref(v_grindProof_710_);
v_a_788_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_724_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_724_);
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
v___jp_717_:
{
size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; 
v___x_719_ = ((size_t)1ULL);
v___x_720_ = lean_usize_add(v_i_699_, v___x_719_);
v___x_721_ = lean_array_uset(v_bs_x27_716_, v_i_699_, v_a_718_);
v_i_699_ = v___x_720_;
v_bs_700_ = v___x_721_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___boxed(lean_object* v_sz_800_, lean_object* v_i_801_, lean_object* v_bs_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
size_t v_sz_boxed_808_; size_t v_i_boxed_809_; lean_object* v_res_810_; 
v_sz_boxed_808_ = lean_unbox_usize(v_sz_800_);
lean_dec(v_sz_800_);
v_i_boxed_809_ = lean_unbox_usize(v_i_801_);
lean_dec(v_i_801_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_boxed_808_, v_i_boxed_809_, v_bs_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(size_t v_sz_811_, size_t v_i_812_, lean_object* v_bs_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_811_, v_i_812_, v_bs_813_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed(lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_bs_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
size_t v_sz_boxed_836_; size_t v_i_boxed_837_; lean_object* v_res_838_; 
v_sz_boxed_836_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_837_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(v_sz_boxed_836_, v_i_boxed_837_, v_bs_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object* v_x_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
lean_inc(v_x_876_);
v___x_899_ = l_Lean_Syntax_isOfKind(v_x_876_, v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v_x_876_);
v___x_900_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_900_;
}
else
{
lean_object* v___x_901_; lean_object* v_cfgStx_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_901_ = lean_unsigned_to_nat(1u);
v_cfgStx_902_ = l_Lean_Syntax_getArg(v_x_876_, v___x_901_);
v___x_903_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_902_);
v___x_904_ = l_Lean_Syntax_isOfKind(v_cfgStx_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_dec(v_cfgStx_902_);
lean_dec(v_x_876_);
v___x_905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_905_;
}
else
{
lean_object* v___x_906_; lean_object* v_tk_907_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v_typesStx_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v_tk_907_ = l_Lean_Syntax_getArg(v_x_876_, v___x_906_);
v___x_1153_ = lean_unsigned_to_nat(2u);
v___x_1154_ = l_Lean_Syntax_getArg(v_x_876_, v___x_1153_);
lean_dec(v_x_876_);
v___x_1155_ = l_Lean_Syntax_isNone(v___x_1154_);
if (v___x_1155_ == 0)
{
uint8_t v___x_1156_; 
lean_inc(v___x_1154_);
v___x_1156_ = l_Lean_Syntax_matchesNull(v___x_1154_, v___x_901_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v___x_1154_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v___x_1157_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1157_;
}
else
{
lean_object* v_typesStx_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_typesStx_1158_ = l_Lean_Syntax_getArg(v___x_1154_, v___x_906_);
lean_dec(v___x_1154_);
v___x_1159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1158_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v_typesStx_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v_typesStx_1158_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v___x_1161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_typesStx_1158_);
v_typesStx_1020_ = v___x_1162_;
v___y_1021_ = v_a_877_;
v___y_1022_ = v_a_878_;
v___y_1023_ = v_a_879_;
v___y_1024_ = v_a_880_;
v___y_1025_ = v_a_881_;
v___y_1026_ = v_a_882_;
v___y_1027_ = v_a_883_;
v___y_1028_ = v_a_884_;
goto v___jp_1019_;
}
}
}
else
{
lean_object* v___x_1163_; 
lean_dec(v___x_1154_);
v___x_1163_ = lean_box(0);
v_typesStx_1020_ = v___x_1163_;
v___y_1021_ = v_a_877_;
v___y_1022_ = v_a_878_;
v___y_1023_ = v_a_879_;
v___y_1024_ = v_a_880_;
v___y_1025_ = v_a_881_;
v___y_1026_ = v_a_882_;
v___y_1027_ = v_a_883_;
v___y_1028_ = v_a_884_;
goto v___jp_1019_;
}
v___jp_908_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_inc_ref(v___y_920_);
v___x_922_ = l_Array_append___redArg(v___y_920_, v___y_921_);
lean_dec_ref(v___y_921_);
lean_inc(v___y_919_);
lean_inc(v___y_915_);
v___x_923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_923_, 0, v___y_915_);
lean_ctor_set(v___x_923_, 1, v___y_919_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
lean_inc(v___y_914_);
v___x_924_ = l_Lean_Syntax_node3(v___y_915_, v___y_914_, v___y_917_, v_cfgStx_902_, v___x_923_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_918_);
v___x_925_ = lean_apply_6(v___y_910_, v___x_924_, v___y_918_, v___y_912_, v___y_913_, v___y_916_, lean_box(0));
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_a_926_);
v___x_929_ = lean_box(0);
v___x_930_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_930_, 0, v___x_928_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
lean_ctor_set(v___x_930_, 2, v___x_929_);
lean_ctor_set(v___x_930_, 3, v___x_929_);
lean_ctor_set(v___x_930_, 4, v___x_929_);
lean_ctor_set(v___x_930_, 5, v___x_929_);
lean_inc(v___y_909_);
v___x_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_931_, 0, v___y_909_);
v___x_932_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_933_ = 4;
v___x_934_ = l_Lean_MessageData_nil;
v___x_935_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_907_, v___x_930_, v___x_931_, v___x_932_, v___x_929_, v___x_933_, v___x_934_, v___y_913_, v___y_916_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_dec_ref_known(v___x_935_, 1);
v___y_887_ = v___y_911_;
v___y_888_ = v___y_918_;
v___y_889_ = v___y_912_;
v___y_890_ = v___y_913_;
v___y_891_ = v___y_916_;
goto v___jp_886_;
}
else
{
return v___x_935_;
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_tk_907_);
v_a_936_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_925_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_925_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
v___jp_944_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc_ref(v___y_955_);
v___x_959_ = l_Array_append___redArg(v___y_955_, v___y_958_);
lean_dec_ref(v___y_958_);
lean_inc(v___y_951_);
lean_inc(v___y_946_);
v___x_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_960_, 0, v___y_946_);
lean_ctor_set(v___x_960_, 1, v___y_951_);
lean_ctor_set(v___x_960_, 2, v___x_959_);
v___x_961_ = lean_box(2);
v___x_962_ = l_Lean_Syntax_mkStrLit(v___y_953_, v___x_961_);
lean_inc(v___y_945_);
v___x_963_ = l_Lean_Syntax_node4(v___y_946_, v___y_945_, v___y_952_, v_cfgStx_902_, v___x_960_, v___x_962_);
lean_inc(v___y_954_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc_ref(v___y_956_);
v___x_964_ = lean_apply_6(v___y_947_, v___x_963_, v___y_956_, v___y_949_, v___y_950_, v___y_954_, lean_box(0));
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v_a_965_);
v___x_968_ = lean_box(0);
v___x_969_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
lean_ctor_set(v___x_969_, 3, v___x_968_);
lean_ctor_set(v___x_969_, 4, v___x_968_);
lean_ctor_set(v___x_969_, 5, v___x_968_);
lean_inc(v___y_957_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v___y_957_);
v___x_971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_972_ = 4;
v___x_973_ = l_Lean_MessageData_nil;
v___x_974_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_907_, v___x_969_, v___x_970_, v___x_971_, v___x_968_, v___x_972_, v___x_973_, v___y_950_, v___y_954_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_dec_ref_known(v___x_974_, 1);
v___y_887_ = v___y_948_;
v___y_888_ = v___y_956_;
v___y_889_ = v___y_949_;
v___y_890_ = v___y_950_;
v___y_891_ = v___y_954_;
goto v___jp_886_;
}
else
{
return v___x_974_;
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_tk_907_);
v_a_975_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_964_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_964_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
v___jp_983_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_inc_ref(v___y_994_);
v___x_997_ = l_Array_append___redArg(v___y_994_, v___y_996_);
lean_dec_ref(v___y_996_);
lean_inc(v___y_988_);
lean_inc(v___y_991_);
v___x_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_998_, 0, v___y_991_);
lean_ctor_set(v___x_998_, 1, v___y_988_);
lean_ctor_set(v___x_998_, 2, v___x_997_);
lean_inc(v___y_989_);
v___x_999_ = l_Lean_Syntax_node3(v___y_991_, v___y_989_, v___y_992_, v_cfgStx_902_, v___x_998_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_987_);
lean_inc(v___y_986_);
lean_inc_ref(v___y_995_);
v___x_1000_ = lean_apply_6(v___y_984_, v___x_999_, v___y_995_, v___y_986_, v___y_987_, v___y_993_, lean_box(0));
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v_a_1001_);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
lean_ctor_set(v___x_1005_, 3, v___x_1004_);
lean_ctor_set(v___x_1005_, 4, v___x_1004_);
lean_ctor_set(v___x_1005_, 5, v___x_1004_);
lean_inc(v___y_990_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___y_990_);
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1008_ = 4;
v___x_1009_ = l_Lean_MessageData_nil;
v___x_1010_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_907_, v___x_1005_, v___x_1006_, v___x_1007_, v___x_1004_, v___x_1008_, v___x_1009_, v___y_987_, v___y_993_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_dec_ref_known(v___x_1010_, 1);
v___y_887_ = v___y_985_;
v___y_888_ = v___y_995_;
v___y_889_ = v___y_986_;
v___y_890_ = v___y_987_;
v___y_891_ = v___y_993_;
goto v___jp_886_;
}
else
{
return v___x_1010_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_tk_907_);
v_a_1011_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1000_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1000_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
v___jp_1019_:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1151_; 
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v___x_1029_, 0);
lean_dec(v_unused_1152_);
v___x_1031_ = v___x_1029_;
v_isShared_1032_ = v_isSharedCheck_1151_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1029_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1151_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1022_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v_mvarId_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v_mvarId_1035_ = lean_ctor_get(v_a_1034_, 1);
lean_inc_n(v_mvarId_1035_, 2);
v___x_1036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5));
lean_inc(v_cfgStx_902_);
v___x_1037_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_902_, v_mvarId_1035_, v___x_1036_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
lean_inc(v_typesStx_1020_);
v___x_1039_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1020_, v_a_1038_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1038_, v_a_1040_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 2);
lean_ctor_set(v___x_1031_, 0, v_a_1034_);
v___x_1044_ = v___x_1031_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1034_);
v___x_1044_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed), 12, 2);
lean_closure_set(v___x_1045_, 0, v___x_1044_);
lean_closure_set(v___x_1045_, 1, v_a_1042_);
v___x_1046_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1045_, v___y_1021_, v___y_1022_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v_lemmas_1048_; lean_object* v_action_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1109_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v_lemmas_1048_ = lean_ctor_get(v_a_1047_, 0);
v_action_1049_ = lean_ctor_get(v_a_1047_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_a_1047_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1051_ = v_a_1047_;
v_isShared_1052_ = v_isSharedCheck_1109_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_action_1049_);
lean_inc(v_lemmas_1048_);
lean_dec(v_a_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1109_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
size_t v_sz_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_sz_1053_ = lean_array_size(v_lemmas_1048_);
v___x_1054_ = lean_box_usize(v_sz_1053_);
v___x_1055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___x_1056_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed), 12, 3);
lean_closure_set(v___x_1056_, 0, v___x_1054_);
lean_closure_set(v___x_1056_, 1, v___x_1055_);
lean_closure_set(v___x_1056_, 2, v_lemmas_1048_);
v___x_1057_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_1035_, v___x_1056_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___f_1060_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1060_, 0, v_a_1058_);
lean_closure_set(v___f_1060_, 1, v___x_1059_);
lean_closure_set(v___f_1060_, 2, v___x_894_);
lean_closure_set(v___f_1060_, 3, v___x_895_);
lean_closure_set(v___f_1060_, 4, v___x_896_);
lean_closure_set(v___f_1060_, 5, v___x_897_);
switch(lean_obj_tag(v_action_1049_))
{
case 0:
{
lean_object* v_ref_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v_ref_1061_ = lean_ctor_get(v___y_1027_, 2);
v___x_1062_ = 0;
v___x_1063_ = l_Lean_SourceInfo_fromRef(v_ref_1061_, v___x_1062_);
v___x_1064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_1065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1063_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 2);
lean_ctor_set(v___x_1051_, 1, v___x_1065_);
lean_ctor_set(v___x_1051_, 0, v___x_1063_);
v___x_1067_ = v___x_1051_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1020_) == 1)
{
lean_object* v_val_1070_; lean_object* v___x_1071_; 
v_val_1070_ = lean_ctor_get(v_typesStx_1020_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v_typesStx_1020_, 1);
v___x_1071_ = l_Array_mkArray1___redArg(v_val_1070_);
v___y_984_ = v___f_1060_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1026_;
v___y_987_ = v___y_1027_;
v___y_988_ = v___x_1068_;
v___y_989_ = v___x_1064_;
v___y_990_ = v_ref_1061_;
v___y_991_ = v___x_1063_;
v___y_992_ = v___x_1067_;
v___y_993_ = v___y_1028_;
v___y_994_ = v___x_1069_;
v___y_995_ = v___y_1025_;
v___y_996_ = v___x_1071_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1072_; 
lean_dec(v_typesStx_1020_);
v___x_1072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_984_ = v___f_1060_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1026_;
v___y_987_ = v___y_1027_;
v___y_988_ = v___x_1068_;
v___y_989_ = v___x_1064_;
v___y_990_ = v_ref_1061_;
v___y_991_ = v___x_1063_;
v___y_992_ = v___x_1067_;
v___y_993_ = v___y_1028_;
v___y_994_ = v___x_1069_;
v___y_995_ = v___y_1025_;
v___y_996_ = v___x_1072_;
goto v___jp_983_;
}
}
}
case 1:
{
lean_object* v_path_1074_; lean_object* v_ref_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_path_1074_ = lean_ctor_get(v_action_1049_, 0);
lean_inc_ref(v_path_1074_);
lean_dec_ref_known(v_action_1049_, 1);
v_ref_1075_ = lean_ctor_get(v___y_1027_, 2);
v___x_1076_ = 0;
v___x_1077_ = l_Lean_SourceInfo_fromRef(v_ref_1075_, v___x_1076_);
v___x_1078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1079_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12));
lean_inc(v___x_1077_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 2);
lean_ctor_set(v___x_1051_, 1, v___x_1079_);
lean_ctor_set(v___x_1051_, 0, v___x_1077_);
v___x_1081_ = v___x_1051_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1083_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1020_) == 1)
{
lean_object* v_val_1084_; lean_object* v___x_1085_; 
v_val_1084_ = lean_ctor_get(v_typesStx_1020_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_typesStx_1020_, 1);
v___x_1085_ = l_Array_mkArray1___redArg(v_val_1084_);
v___y_945_ = v___x_1078_;
v___y_946_ = v___x_1077_;
v___y_947_ = v___f_1060_;
v___y_948_ = v___y_1022_;
v___y_949_ = v___y_1026_;
v___y_950_ = v___y_1027_;
v___y_951_ = v___x_1082_;
v___y_952_ = v___x_1081_;
v___y_953_ = v_path_1074_;
v___y_954_ = v___y_1028_;
v___y_955_ = v___x_1083_;
v___y_956_ = v___y_1025_;
v___y_957_ = v_ref_1075_;
v___y_958_ = v___x_1085_;
goto v___jp_944_;
}
else
{
lean_object* v___x_1086_; 
lean_dec(v_typesStx_1020_);
v___x_1086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_945_ = v___x_1078_;
v___y_946_ = v___x_1077_;
v___y_947_ = v___f_1060_;
v___y_948_ = v___y_1022_;
v___y_949_ = v___y_1026_;
v___y_950_ = v___y_1027_;
v___y_951_ = v___x_1082_;
v___y_952_ = v___x_1081_;
v___y_953_ = v_path_1074_;
v___y_954_ = v___y_1028_;
v___y_955_ = v___x_1083_;
v___y_956_ = v___y_1025_;
v___y_957_ = v_ref_1075_;
v___y_958_ = v___x_1086_;
goto v___jp_944_;
}
}
}
default: 
{
lean_object* v_ref_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_ref_1088_ = lean_ctor_get(v___y_1027_, 2);
v___x_1089_ = 0;
v___x_1090_ = l_Lean_SourceInfo_fromRef(v_ref_1088_, v___x_1089_);
v___x_1091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6));
lean_inc(v___x_1090_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 2);
lean_ctor_set(v___x_1051_, 1, v___x_1092_);
lean_ctor_set(v___x_1051_, 0, v___x_1090_);
v___x_1094_ = v___x_1051_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1096_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1020_) == 1)
{
lean_object* v_val_1097_; lean_object* v___x_1098_; 
v_val_1097_ = lean_ctor_get(v_typesStx_1020_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_typesStx_1020_, 1);
v___x_1098_ = l_Array_mkArray1___redArg(v_val_1097_);
v___y_909_ = v_ref_1088_;
v___y_910_ = v___f_1060_;
v___y_911_ = v___y_1022_;
v___y_912_ = v___y_1026_;
v___y_913_ = v___y_1027_;
v___y_914_ = v___x_1091_;
v___y_915_ = v___x_1090_;
v___y_916_ = v___y_1028_;
v___y_917_ = v___x_1094_;
v___y_918_ = v___y_1025_;
v___y_919_ = v___x_1095_;
v___y_920_ = v___x_1096_;
v___y_921_ = v___x_1098_;
goto v___jp_908_;
}
else
{
lean_object* v___x_1099_; 
lean_dec(v_typesStx_1020_);
v___x_1099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_909_ = v_ref_1088_;
v___y_910_ = v___f_1060_;
v___y_911_ = v___y_1022_;
v___y_912_ = v___y_1026_;
v___y_913_ = v___y_1027_;
v___y_914_ = v___x_1091_;
v___y_915_ = v___x_1090_;
v___y_916_ = v___y_1028_;
v___y_917_ = v___x_1094_;
v___y_918_ = v___y_1025_;
v___y_919_ = v___x_1095_;
v___y_920_ = v___x_1096_;
v___y_921_ = v___x_1099_;
goto v___jp_908_;
}
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_del_object(v___x_1051_);
lean_dec(v_action_1049_);
lean_dec(v_typesStx_1020_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v_a_1101_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1057_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1057_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_mvarId_1035_);
lean_dec(v_typesStx_1020_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v_a_1110_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1046_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1046_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_mvarId_1035_);
lean_dec(v_a_1034_);
lean_del_object(v___x_1031_);
lean_dec(v_typesStx_1020_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v_a_1119_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1041_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1041_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1038_);
lean_dec(v_mvarId_1035_);
lean_dec(v_a_1034_);
lean_del_object(v___x_1031_);
lean_dec(v_typesStx_1020_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v_a_1127_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1039_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1039_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_mvarId_1035_);
lean_dec(v_a_1034_);
lean_del_object(v___x_1031_);
lean_dec(v_typesStx_1020_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v_a_1135_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1037_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1037_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
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
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_del_object(v___x_1031_);
lean_dec(v_typesStx_1020_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
v_a_1143_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1033_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1033_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1020_);
lean_dec(v_tk_907_);
lean_dec(v_cfgStx_902_);
return v___x_1029_;
}
}
}
}
v___jp_886_:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_box(0);
v___x_893_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_892_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object* v_x_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(v_x_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(size_t v_sz_1175_, size_t v_i_1176_, lean_object* v_bs_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_1175_, v_i_1176_, v_bs_1177_, v___y_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___boxed(lean_object* v_sz_1184_, lean_object* v_i_1185_, lean_object* v_bs_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
size_t v_sz_boxed_1192_; size_t v_i_boxed_1193_; lean_object* v_res_1194_; 
v_sz_boxed_1192_ = lean_unbox_usize(v_sz_1184_);
lean_dec(v_sz_1184_);
v_i_boxed_1193_ = lean_unbox_usize(v_i_1185_);
lean_dec(v_i_1185_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(v_sz_boxed_1192_, v_i_boxed_1193_, v_bs_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1(){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1200_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1));
v___x_1203_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed), 10, 0);
v___x_1204_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1200_, v___x_1201_, v___x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___boxed(lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1207_, lean_object* v_opt_1208_){
_start:
{
lean_object* v_name_1209_; lean_object* v_defValue_1210_; lean_object* v_map_1211_; lean_object* v___x_1212_; 
v_name_1209_ = lean_ctor_get(v_opt_1208_, 0);
v_defValue_1210_ = lean_ctor_get(v_opt_1208_, 1);
v_map_1211_ = lean_ctor_get(v_opts_1207_, 0);
v___x_1212_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1211_, v_name_1209_);
if (lean_obj_tag(v___x_1212_) == 0)
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_unbox(v_defValue_1210_);
return v___x_1213_;
}
else
{
lean_object* v_val_1214_; 
v_val_1214_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_val_1214_);
lean_dec_ref_known(v___x_1212_, 1);
if (lean_obj_tag(v_val_1214_) == 1)
{
uint8_t v_v_1215_; 
v_v_1215_ = lean_ctor_get_uint8(v_val_1214_, 0);
lean_dec_ref_known(v_val_1214_, 0);
return v_v_1215_;
}
else
{
uint8_t v___x_1216_; 
lean_dec(v_val_1214_);
v___x_1216_ = lean_unbox(v_defValue_1210_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1217_, lean_object* v_opt_1218_){
_start:
{
uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_res_1219_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v_opts_1217_, v_opt_1218_);
lean_dec_ref(v_opt_1218_);
lean_dec_ref(v_opts_1217_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1228_) == 1)
{
lean_object* v_pre_1229_; 
v_pre_1229_ = lean_ctor_get(v_x_1228_, 0);
switch(lean_obj_tag(v_pre_1229_))
{
case 1:
{
lean_object* v_pre_1230_; 
v_pre_1230_ = lean_ctor_get(v_pre_1229_, 0);
switch(lean_obj_tag(v_pre_1230_))
{
case 0:
{
lean_object* v_str_1231_; lean_object* v_str_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_str_1231_ = lean_ctor_get(v_x_1228_, 1);
v_str_1232_ = lean_ctor_get(v_pre_1229_, 1);
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3));
v___x_1234_ = lean_string_dec_eq(v_str_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1236_ = lean_string_dec_eq(v_str_1232_, v___x_1235_);
if (v___x_1236_ == 0)
{
return v___x_1236_;
}
else
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1238_ = lean_string_dec_eq(v_str_1231_, v___x_1237_);
if (v___x_1238_ == 0)
{
return v___x_1238_;
}
else
{
return v_suppressElabErrors_1227_;
}
}
}
else
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1240_ = lean_string_dec_eq(v_str_1231_, v___x_1239_);
if (v___x_1240_ == 0)
{
return v___x_1240_;
}
else
{
return v_suppressElabErrors_1227_;
}
}
}
case 1:
{
lean_object* v_pre_1241_; 
v_pre_1241_ = lean_ctor_get(v_pre_1230_, 0);
if (lean_obj_tag(v_pre_1241_) == 0)
{
lean_object* v_str_1242_; lean_object* v_str_1243_; lean_object* v_str_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_str_1242_ = lean_ctor_get(v_x_1228_, 1);
v_str_1243_ = lean_ctor_get(v_pre_1229_, 1);
v_str_1244_ = lean_ctor_get(v_pre_1230_, 1);
v___x_1245_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1246_ = lean_string_dec_eq(v_str_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
return v___x_1246_;
}
else
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1248_ = lean_string_dec_eq(v_str_1243_, v___x_1247_);
if (v___x_1248_ == 0)
{
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1250_ = lean_string_dec_eq(v_str_1242_, v___x_1249_);
if (v___x_1250_ == 0)
{
return v___x_1250_;
}
else
{
return v_suppressElabErrors_1227_;
}
}
}
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = 0;
return v___x_1251_;
}
}
default: 
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
}
}
case 0:
{
lean_object* v_str_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_str_1253_ = lean_ctor_get(v_x_1228_, 1);
v___x_1254_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1255_ = lean_string_dec_eq(v_str_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
return v___x_1255_;
}
else
{
return v_suppressElabErrors_1227_;
}
}
default: 
{
uint8_t v___x_1256_; 
v___x_1256_ = 0;
return v___x_1256_;
}
}
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = 0;
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1258_, lean_object* v_x_1259_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1260_; uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_suppressElabErrors_boxed_1260_ = lean_unbox(v_suppressElabErrors_1258_);
v_res_1261_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1260_, v_x_1259_);
lean_dec(v_x_1259_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; lean_object* v_env_1270_; uint8_t v___x_1271_; lean_object* v_env_1272_; lean_object* v___x_1273_; lean_object* v_toCold_1274_; lean_object* v_mctx_1275_; lean_object* v_lctx_1276_; lean_object* v_options_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1269_ = lean_st_ref_get(v___y_1267_);
v_env_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc_ref(v_env_1270_);
lean_dec(v___x_1269_);
v___x_1271_ = 0;
v_env_1272_ = l_Lean_Environment_setRecordingDeps(v_env_1270_, v___x_1271_);
v___x_1273_ = lean_st_ref_get(v___y_1265_);
v_toCold_1274_ = lean_ctor_get(v___y_1266_, 0);
v_mctx_1275_ = lean_ctor_get(v___x_1273_, 0);
lean_inc_ref(v_mctx_1275_);
lean_dec(v___x_1273_);
v_lctx_1276_ = lean_ctor_get(v___y_1264_, 2);
v_options_1277_ = lean_ctor_get(v_toCold_1274_, 2);
lean_inc_ref(v_options_1277_);
lean_inc_ref(v_lctx_1276_);
v___x_1278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1278_, 0, v_env_1272_);
lean_ctor_set(v___x_1278_, 1, v_mctx_1275_);
lean_ctor_set(v___x_1278_, 2, v_lctx_1276_);
lean_ctor_set(v___x_1278_, 3, v_options_1277_);
v___x_1279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_msgData_1263_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msgData_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object* v_ref_1288_, lean_object* v_msgData_1289_, uint8_t v_severity_1290_, uint8_t v_isSilent_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___y_1298_; lean_object* v___y_1299_; uint8_t v___y_1300_; uint8_t v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v_toCold_1305_; lean_object* v___y_1306_; lean_object* v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1337_; uint8_t v___y_1338_; lean_object* v___y_1339_; uint8_t v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; uint8_t v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1372_; uint8_t v___y_1373_; uint8_t v___x_1383_; uint8_t v___y_1385_; uint8_t v___x_1391_; 
v___x_1383_ = 2;
v___x_1391_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1290_, v___x_1383_);
if (v___x_1391_ == 0)
{
v___y_1385_ = v___x_1391_;
goto v___jp_1384_;
}
else
{
uint8_t v___x_1392_; 
lean_inc_ref(v_msgData_1289_);
v___x_1392_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1289_);
if (v___x_1392_ == 0)
{
v___y_1385_ = v___x_1392_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec_ref(v_msgData_1289_);
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
}
v___jp_1297_:
{
lean_object* v_currNamespace_1307_; lean_object* v_openDecls_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_env_1313_; lean_object* v_nextMacroScope_1314_; lean_object* v_ngen_1315_; lean_object* v_auxDeclNGen_1316_; lean_object* v_traceState_1317_; lean_object* v_cache_1318_; lean_object* v_recordedDeps_1319_; lean_object* v_messages_1320_; lean_object* v_infoState_1321_; lean_object* v_snapshotTasks_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1333_; 
v_currNamespace_1307_ = lean_ctor_get(v_toCold_1305_, 4);
v_openDecls_1308_ = lean_ctor_get(v_toCold_1305_, 5);
lean_inc(v_openDecls_1308_);
lean_inc(v_currNamespace_1307_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_currNamespace_1307_);
lean_ctor_set(v___x_1309_, 1, v_openDecls_1308_);
v___x_1310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___y_1304_);
lean_inc_ref(v___y_1298_);
lean_inc_ref(v___y_1299_);
v___x_1311_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1311_, 0, v___y_1299_);
lean_ctor_set(v___x_1311_, 1, v___y_1302_);
lean_ctor_set(v___x_1311_, 2, v___y_1303_);
lean_ctor_set(v___x_1311_, 3, v___y_1298_);
lean_ctor_set(v___x_1311_, 4, v___x_1310_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5, v___y_1300_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5 + 1, v___y_1301_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*5 + 2, v_isSilent_1291_);
v___x_1312_ = lean_st_ref_take(v___y_1306_);
v_env_1313_ = lean_ctor_get(v___x_1312_, 0);
v_nextMacroScope_1314_ = lean_ctor_get(v___x_1312_, 1);
v_ngen_1315_ = lean_ctor_get(v___x_1312_, 2);
v_auxDeclNGen_1316_ = lean_ctor_get(v___x_1312_, 3);
v_traceState_1317_ = lean_ctor_get(v___x_1312_, 4);
v_cache_1318_ = lean_ctor_get(v___x_1312_, 5);
v_recordedDeps_1319_ = lean_ctor_get(v___x_1312_, 6);
v_messages_1320_ = lean_ctor_get(v___x_1312_, 7);
v_infoState_1321_ = lean_ctor_get(v___x_1312_, 8);
v_snapshotTasks_1322_ = lean_ctor_get(v___x_1312_, 9);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1324_ = v___x_1312_;
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snapshotTasks_1322_);
lean_inc(v_infoState_1321_);
lean_inc(v_messages_1320_);
lean_inc(v_recordedDeps_1319_);
lean_inc(v_cache_1318_);
lean_inc(v_traceState_1317_);
lean_inc(v_auxDeclNGen_1316_);
lean_inc(v_ngen_1315_);
lean_inc(v_nextMacroScope_1314_);
lean_inc(v_env_1313_);
lean_dec(v___x_1312_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = l_Lean_MessageLog_add(v___x_1311_, v_messages_1320_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 7, v___x_1327_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_env_1313_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_nextMacroScope_1314_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_ngen_1315_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_auxDeclNGen_1316_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_traceState_1317_);
lean_ctor_set(v_reuseFailAlloc_1332_, 5, v_cache_1318_);
lean_ctor_set(v_reuseFailAlloc_1332_, 6, v_recordedDeps_1319_);
lean_ctor_set(v_reuseFailAlloc_1332_, 7, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1332_, 8, v_infoState_1321_);
lean_ctor_set(v_reuseFailAlloc_1332_, 9, v_snapshotTasks_1322_);
v___x_1329_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = lean_st_ref_put(v___y_1306_, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1326_);
return v___x_1331_;
}
}
}
v___jp_1334_:
{
lean_object* v_fileName_1343_; lean_object* v_fileMap_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1360_; 
v_fileName_1343_ = lean_ctor_get(v___y_1339_, 0);
v_fileMap_1344_ = lean_ctor_get(v___y_1339_, 1);
v___x_1345_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1289_);
v___x_1346_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v___x_1345_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1360_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1360_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_inc_ref_n(v_fileMap_1344_, 2);
v___x_1351_ = l_Lean_FileMap_toPosition(v_fileMap_1344_, v___y_1341_);
lean_dec(v___y_1341_);
v___x_1352_ = l_Lean_FileMap_toPosition(v_fileMap_1344_, v___y_1342_);
lean_dec(v___y_1342_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
v___x_1354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
if (v___y_1340_ == 0)
{
lean_del_object(v___x_1349_);
lean_dec_ref(v___y_1335_);
v___y_1298_ = v___x_1354_;
v___y_1299_ = v_fileName_1343_;
v___y_1300_ = v___y_1337_;
v___y_1301_ = v___y_1338_;
v___y_1302_ = v___x_1351_;
v___y_1303_ = v___x_1353_;
v___y_1304_ = v_a_1347_;
v_toCold_1305_ = v___y_1336_;
v___y_1306_ = v___y_1295_;
goto v___jp_1297_;
}
else
{
uint8_t v___x_1355_; 
lean_inc(v_a_1347_);
v___x_1355_ = l_Lean_MessageData_hasTag(v___y_1335_, v_a_1347_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_dec_ref_known(v___x_1353_, 1);
lean_dec_ref(v___x_1351_);
lean_dec(v_a_1347_);
v___x_1356_ = lean_box(0);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1356_);
v___x_1358_ = v___x_1349_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
else
{
lean_del_object(v___x_1349_);
v___y_1298_ = v___x_1354_;
v___y_1299_ = v_fileName_1343_;
v___y_1300_ = v___y_1337_;
v___y_1301_ = v___y_1338_;
v___y_1302_ = v___x_1351_;
v___y_1303_ = v___x_1353_;
v___y_1304_ = v_a_1347_;
v_toCold_1305_ = v___y_1336_;
v___y_1306_ = v___y_1295_;
goto v___jp_1297_;
}
}
}
}
v___jp_1361_:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Syntax_getTailPos_x3f(v___y_1367_, v___y_1365_);
lean_dec(v___y_1367_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_inc(v___y_1368_);
v___y_1335_ = v___y_1362_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1365_;
v___y_1338_ = v___y_1366_;
v___y_1339_ = v___y_1363_;
v___y_1340_ = v___y_1364_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v___y_1368_;
goto v___jp_1334_;
}
else
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___y_1335_ = v___y_1362_;
v___y_1336_ = v___y_1363_;
v___y_1337_ = v___y_1365_;
v___y_1338_ = v___y_1366_;
v___y_1339_ = v___y_1363_;
v___y_1340_ = v___y_1364_;
v___y_1341_ = v___y_1368_;
v___y_1342_ = v_val_1370_;
goto v___jp_1334_;
}
}
v___jp_1371_:
{
lean_object* v_toCold_1374_; lean_object* v_ref_1375_; uint8_t v_suppressElabErrors_1376_; lean_object* v___x_1377_; lean_object* v___f_1378_; lean_object* v_ref_1379_; lean_object* v___x_1380_; 
v_toCold_1374_ = lean_ctor_get(v___y_1294_, 0);
v_ref_1375_ = lean_ctor_get(v___y_1294_, 2);
v_suppressElabErrors_1376_ = lean_ctor_get_uint8(v___y_1294_, sizeof(void*)*3 + 2);
v___x_1377_ = lean_box(v_suppressElabErrors_1376_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1378_, 0, v___x_1377_);
v_ref_1379_ = l_Lean_replaceRef(v_ref_1288_, v_ref_1375_);
v___x_1380_ = l_Lean_Syntax_getPos_x3f(v_ref_1379_, v___y_1372_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___y_1362_ = v___f_1378_;
v___y_1363_ = v_toCold_1374_;
v___y_1364_ = v_suppressElabErrors_1376_;
v___y_1365_ = v___y_1372_;
v___y_1366_ = v___y_1373_;
v___y_1367_ = v_ref_1379_;
v___y_1368_ = v___x_1381_;
goto v___jp_1361_;
}
else
{
lean_object* v_val_1382_; 
v_val_1382_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v___x_1380_, 1);
v___y_1362_ = v___f_1378_;
v___y_1363_ = v_toCold_1374_;
v___y_1364_ = v_suppressElabErrors_1376_;
v___y_1365_ = v___y_1372_;
v___y_1366_ = v___y_1373_;
v___y_1367_ = v_ref_1379_;
v___y_1368_ = v_val_1382_;
goto v___jp_1361_;
}
}
v___jp_1384_:
{
uint8_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = 1;
v___x_1387_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1290_, v___x_1386_);
if (v___x_1387_ == 0)
{
v___y_1372_ = v___y_1385_;
v___y_1373_ = v_severity_1290_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1294_);
v___x_1389_ = l_Lean_warningAsError;
v___x_1390_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v___x_1388_, v___x_1389_);
lean_dec_ref(v___x_1388_);
if (v___x_1390_ == 0)
{
v___y_1372_ = v___y_1385_;
v___y_1373_ = v_severity_1290_;
goto v___jp_1371_;
}
else
{
v___y_1372_ = v___y_1385_;
v___y_1373_ = v___x_1383_;
goto v___jp_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1395_, lean_object* v_msgData_1396_, lean_object* v_severity_1397_, lean_object* v_isSilent_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_severity_boxed_1404_; uint8_t v_isSilent_boxed_1405_; lean_object* v_res_1406_; 
v_severity_boxed_1404_ = lean_unbox(v_severity_1397_);
v_isSilent_boxed_1405_ = lean_unbox(v_isSilent_1398_);
v_res_1406_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1395_, v_msgData_1396_, v_severity_boxed_1404_, v_isSilent_boxed_1405_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v_ref_1395_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object* v_msgData_1407_, uint8_t v_severity_1408_, uint8_t v_isSilent_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_ref_1415_; lean_object* v___x_1416_; 
v_ref_1415_ = lean_ctor_get(v___y_1412_, 2);
v___x_1416_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1415_, v_msgData_1407_, v_severity_1408_, v_isSilent_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object* v_msgData_1417_, lean_object* v_severity_1418_, lean_object* v_isSilent_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v_severity_boxed_1425_; uint8_t v_isSilent_boxed_1426_; lean_object* v_res_1427_; 
v_severity_boxed_1425_ = lean_unbox(v_severity_1418_);
v_isSilent_boxed_1426_ = lean_unbox(v_isSilent_1419_);
v_res_1427_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1417_, v_severity_boxed_1425_, v_isSilent_boxed_1426_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object* v_msgData_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v___x_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = 1;
v___x_1435_ = 0;
v___x_1436_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1428_, v___x_1434_, v___x_1435_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object* v_msgData_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v_msgData_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1443_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object* v___x_1450_, lean_object* v___x_1451_, lean_object* v___x_1452_, lean_object* v___x_1453_, lean_object* v_cfgStx_1454_, lean_object* v_tk_1455_, lean_object* v_typesStx_1456_, lean_object* v___x_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_ref_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___y_1474_; 
v_ref_1463_ = lean_ctor_get(v___y_1460_, 2);
v___x_1464_ = 0;
v___x_1465_ = l_Lean_SourceInfo_fromRef(v_ref_1463_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1));
v___x_1467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6));
v___x_1468_ = l_Lean_Name_mkStr5(v___x_1450_, v___x_1451_, v___x_1452_, v___x_1453_, v___x_1467_);
v___x_1469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1465_);
v___x_1470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1465_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1456_) == 1)
{
lean_object* v_val_1495_; lean_object* v___x_1496_; 
v_val_1495_ = lean_ctor_get(v_typesStx_1456_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v_typesStx_1456_, 1);
v___x_1496_ = l_Array_mkArray1___redArg(v_val_1495_);
v___y_1474_ = v___x_1496_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1497_; 
lean_dec(v_typesStx_1456_);
v___x_1497_ = lean_mk_empty_array_with_capacity(v___x_1457_);
v___y_1474_ = v___x_1497_;
goto v___jp_1473_;
}
v___jp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1475_ = l_Array_append___redArg(v___x_1472_, v___y_1474_);
lean_dec_ref(v___y_1474_);
lean_inc(v___x_1465_);
v___x_1476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1465_);
lean_ctor_set(v___x_1476_, 1, v___x_1471_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
v___x_1477_ = l_Lean_Syntax_node3(v___x_1465_, v___x_1468_, v___x_1470_, v_cfgStx_1454_, v___x_1476_);
v___x_1478_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3);
v___x_1479_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v___x_1478_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1493_; 
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v___x_1479_, 0);
lean_dec(v_unused_1494_);
v___x_1481_ = v___x_1479_;
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v___x_1479_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1493_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1466_);
lean_ctor_set(v___x_1483_, 1, v___x_1477_);
v___x_1484_ = lean_box(0);
v___x_1485_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_ctor_set(v___x_1485_, 3, v___x_1484_);
lean_ctor_set(v___x_1485_, 4, v___x_1484_);
lean_ctor_set(v___x_1485_, 5, v___x_1484_);
lean_inc(v_ref_1463_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 1);
lean_ctor_set(v___x_1481_, 0, v_ref_1463_);
v___x_1487_ = v___x_1481_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_ref_1463_);
v___x_1487_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1489_ = 4;
v___x_1490_ = l_Lean_MessageData_nil;
v___x_1491_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1455_, v___x_1485_, v___x_1487_, v___x_1488_, v___x_1484_, v___x_1489_, v___x_1490_, v___y_1460_, v___y_1461_);
return v___x_1491_;
}
}
}
else
{
lean_dec(v___x_1477_);
lean_dec(v_tk_1455_);
return v___x_1479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object* v___x_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v___x_1501_, lean_object* v_cfgStx_1502_, lean_object* v_tk_1503_, lean_object* v_typesStx_1504_, lean_object* v___x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(v___x_1498_, v___x_1499_, v___x_1500_, v___x_1501_, v_cfgStx_1502_, v_tk_1503_, v_typesStx_1504_, v___x_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___x_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(lean_object* v_x_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
lean_inc(v_x_1517_);
v___x_1532_ = l_Lean_Syntax_isOfKind(v_x_1517_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_dec(v_x_1517_);
v___x_1533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; lean_object* v_cfgStx_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1534_ = lean_unsigned_to_nat(1u);
v_cfgStx_1535_ = l_Lean_Syntax_getArg(v_x_1517_, v___x_1534_);
v___x_1536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_1535_);
v___x_1537_ = l_Lean_Syntax_isOfKind(v_cfgStx_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec(v_cfgStx_1535_);
lean_dec(v_x_1517_);
v___x_1538_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v_tk_1540_; lean_object* v_typesStx_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v_tk_1540_ = l_Lean_Syntax_getArg(v_x_1517_, v___x_1539_);
v___x_1613_ = lean_unsigned_to_nat(2u);
v___x_1614_ = l_Lean_Syntax_getArg(v_x_1517_, v___x_1613_);
v___x_1615_ = l_Lean_Syntax_isNone(v___x_1614_);
if (v___x_1615_ == 0)
{
uint8_t v___x_1616_; 
lean_inc(v___x_1614_);
v___x_1616_ = l_Lean_Syntax_matchesNull(v___x_1614_, v___x_1534_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; 
lean_dec(v___x_1614_);
lean_dec(v_tk_1540_);
lean_dec(v_cfgStx_1535_);
lean_dec(v_x_1517_);
v___x_1617_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1617_;
}
else
{
lean_object* v_typesStx_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_typesStx_1618_ = l_Lean_Syntax_getArg(v___x_1614_, v___x_1539_);
lean_dec(v___x_1614_);
v___x_1619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1618_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v_typesStx_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v_typesStx_1618_);
lean_dec(v_tk_1540_);
lean_dec(v_cfgStx_1535_);
lean_dec(v_x_1517_);
v___x_1621_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v_typesStx_1618_);
v_typesStx_1542_ = v___x_1622_;
v___y_1543_ = v_a_1518_;
v___y_1544_ = v_a_1519_;
v___y_1545_ = v_a_1520_;
v___y_1546_ = v_a_1521_;
v___y_1547_ = v_a_1522_;
v___y_1548_ = v_a_1523_;
v___y_1549_ = v_a_1524_;
v___y_1550_ = v_a_1525_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1623_; 
lean_dec(v___x_1614_);
v___x_1623_ = lean_box(0);
v_typesStx_1542_ = v___x_1623_;
v___y_1543_ = v_a_1518_;
v___y_1544_ = v_a_1519_;
v___y_1545_ = v_a_1520_;
v___y_1546_ = v_a_1521_;
v___y_1547_ = v_a_1522_;
v___y_1548_ = v_a_1523_;
v___y_1549_ = v_a_1524_;
v___y_1550_ = v_a_1525_;
goto v___jp_1541_;
}
v___jp_1541_:
{
lean_object* v___x_1551_; lean_object* v_path_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1551_ = lean_unsigned_to_nat(3u);
v_path_1552_ = l_Lean_Syntax_getArg(v_x_1517_, v___x_1551_);
lean_dec(v_x_1517_);
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1));
lean_inc(v_path_1552_);
v___x_1554_ = l_Lean_Syntax_isOfKind(v_path_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_dec(v_path_1552_);
lean_dec(v_typesStx_1542_);
lean_dec(v_tk_1540_);
lean_dec(v_cfgStx_1535_);
v___x_1555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1555_;
}
else
{
lean_object* v___f_1556_; lean_object* v___x_1557_; 
lean_inc(v_typesStx_1542_);
lean_inc(v_cfgStx_1535_);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1556_, 0, v___x_1527_);
lean_closure_set(v___f_1556_, 1, v___x_1528_);
lean_closure_set(v___f_1556_, 2, v___x_1529_);
lean_closure_set(v___f_1556_, 3, v___x_1530_);
lean_closure_set(v___f_1556_, 4, v_cfgStx_1535_);
lean_closure_set(v___f_1556_, 5, v_tk_1540_);
lean_closure_set(v___f_1556_, 6, v_typesStx_1542_);
lean_closure_set(v___f_1556_, 7, v___x_1539_);
v___x_1557_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1611_; 
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1557_, 0);
lean_dec(v_unused_1612_);
v___x_1559_ = v___x_1557_;
v_isShared_1560_ = v_isSharedCheck_1611_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v___x_1557_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1611_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1544_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_mvarId_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_mvarId_1563_ = lean_ctor_get(v_a_1562_, 1);
v___x_1564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2));
lean_inc(v_mvarId_1563_);
v___x_1565_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_1535_, v_mvarId_1563_, v___x_1564_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1542_, v_a_1566_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = l_Lean_TSyntax_getString(v_path_1552_);
lean_dec(v_path_1552_);
v___x_1570_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_1569_, v_a_1566_, v_a_1568_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
if (v_isShared_1560_ == 0)
{
lean_ctor_set_tag(v___x_1559_, 2);
lean_ctor_set(v___x_1559_, 0, v_a_1562_);
v___x_1573_ = v___x_1559_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1562_);
v___x_1573_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_1574_, 0, v___x_1573_);
lean_closure_set(v___x_1574_, 1, v_a_1571_);
lean_closure_set(v___x_1574_, 2, v___f_1556_);
v___x_1575_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1574_, v___y_1543_, v___y_1544_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1575_, 1);
v___x_1576_ = lean_box(0);
v___x_1577_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1576_, v___y_1544_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1577_;
}
else
{
return v___x_1575_;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1562_);
lean_del_object(v___x_1559_);
lean_dec_ref(v___f_1556_);
v_a_1579_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1570_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1570_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_a_1566_);
lean_dec(v_a_1562_);
lean_del_object(v___x_1559_);
lean_dec_ref(v___f_1556_);
lean_dec(v_path_1552_);
v_a_1587_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1567_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1567_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1562_);
lean_del_object(v___x_1559_);
lean_dec_ref(v___f_1556_);
lean_dec(v_path_1552_);
lean_dec(v_typesStx_1542_);
v_a_1595_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1565_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1565_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_del_object(v___x_1559_);
lean_dec_ref(v___f_1556_);
lean_dec(v_path_1552_);
lean_dec(v_typesStx_1542_);
lean_dec(v_cfgStx_1535_);
v_a_1603_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1561_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1561_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_1556_);
lean_dec(v_path_1552_);
lean_dec(v_typesStx_1542_);
lean_dec(v_cfgStx_1535_);
return v___x_1557_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed(lean_object* v_x_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(v_x_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1(){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1640_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1642_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1));
v___x_1643_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed), 10, 0);
v___x_1644_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1640_, v___x_1641_, v___x_1642_, v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___boxed(lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
return v_res_1646_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1);
v___x_1651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
lean_ctor_set(v___x_1651_, 2, v___x_1650_);
lean_ctor_set(v___x_1651_, 3, v___x_1650_);
return v___x_1651_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_unsigned_to_nat(16u);
v___x_1654_ = lean_mk_array(v___x_1653_, v___x_1652_);
return v___x_1654_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3);
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___x_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4);
v___x_1659_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
lean_ctor_set(v___x_1659_, 3, v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__7));
v___x_1665_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4);
v___x_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
lean_ctor_set(v___x_1666_, 2, v___x_1665_);
lean_ctor_set(v___x_1666_, 3, v___x_1664_);
lean_ctor_set(v___x_1666_, 4, v___x_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v___x_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1680_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_1681_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_1682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_1683_ = 0;
v___x_1684_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8);
v___x_1685_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1685_, 0, v___x_1680_);
lean_ctor_set(v___x_1685_, 1, v___x_1681_);
lean_ctor_set(v___x_1685_, 2, v___x_1667_);
lean_ctor_set(v___x_1685_, 3, v___x_1682_);
lean_ctor_set(v___x_1685_, 4, v___x_1684_);
lean_ctor_set_uint8(v___x_1685_, sizeof(void*)*5, v___x_1683_);
v___x_1686_ = lean_st_mk_ref(v___x_1685_);
v___x_1687_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1668_, v___x_1669_, v___x_1686_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1697_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1697_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1692_ = lean_st_ref_get(v___x_1686_);
lean_dec(v___x_1686_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_a_1688_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1693_);
v___x_1695_ = v___x_1690_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v___x_1686_);
v_a_1698_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1687_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1687_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object* v___x_1706_, lean_object* v___x_1707_, lean_object* v___x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(v___x_1706_, v___x_1707_, v___x_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___x_1708_);
lean_dec(v___x_1707_);
return v_res_1719_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1720_, lean_object* v_i_1721_, lean_object* v_k_1722_){
_start:
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = lean_array_get_size(v_keys_1720_);
v___x_1724_ = lean_nat_dec_lt(v_i_1721_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_dec(v_i_1721_);
return v___x_1724_;
}
else
{
lean_object* v_k_x27_1725_; uint8_t v___x_1726_; 
v_k_x27_1725_ = lean_array_fget_borrowed(v_keys_1720_, v_i_1721_);
v___x_1726_ = l_Lean_instBEqMVarId_beq(v_k_1722_, v_k_x27_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v_i_1721_, v___x_1727_);
lean_dec(v_i_1721_);
v_i_1721_ = v___x_1728_;
goto _start;
}
else
{
lean_dec(v_i_1721_);
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1730_, lean_object* v_i_1731_, lean_object* v_k_1732_){
_start:
{
uint8_t v_res_1733_; lean_object* v_r_1734_; 
v_res_1733_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1730_, v_i_1731_, v_k_1732_);
lean_dec(v_k_1732_);
lean_dec_ref(v_keys_1730_);
v_r_1734_ = lean_box(v_res_1733_);
return v_r_1734_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1735_, size_t v_x_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1735_) == 0)
{
lean_object* v_es_1738_; lean_object* v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; lean_object* v_j_1742_; lean_object* v___x_1743_; 
v_es_1738_ = lean_ctor_get(v_x_1735_, 0);
v___x_1739_ = lean_box(2);
v___x_1740_ = ((size_t)31ULL);
v___x_1741_ = lean_usize_land(v_x_1736_, v___x_1740_);
v_j_1742_ = lean_usize_to_nat(v___x_1741_);
v___x_1743_ = lean_array_get_borrowed(v___x_1739_, v_es_1738_, v_j_1742_);
lean_dec(v_j_1742_);
switch(lean_obj_tag(v___x_1743_))
{
case 0:
{
lean_object* v_key_1744_; uint8_t v___x_1745_; 
v_key_1744_ = lean_ctor_get(v___x_1743_, 0);
v___x_1745_ = l_Lean_instBEqMVarId_beq(v_x_1737_, v_key_1744_);
return v___x_1745_;
}
case 1:
{
lean_object* v_node_1746_; size_t v___x_1747_; size_t v___x_1748_; 
v_node_1746_ = lean_ctor_get(v___x_1743_, 0);
v___x_1747_ = ((size_t)5ULL);
v___x_1748_ = lean_usize_shift_right(v_x_1736_, v___x_1747_);
v_x_1735_ = v_node_1746_;
v_x_1736_ = v___x_1748_;
goto _start;
}
default: 
{
uint8_t v___x_1750_; 
v___x_1750_ = 0;
return v___x_1750_;
}
}
}
else
{
lean_object* v_ks_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v_ks_1751_ = lean_ctor_get(v_x_1735_, 0);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1751_, v___x_1752_, v_x_1737_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
size_t v_x_3535__boxed_1757_; uint8_t v_res_1758_; lean_object* v_r_1759_; 
v_x_3535__boxed_1757_ = lean_unbox_usize(v_x_1755_);
lean_dec(v_x_1755_);
v_res_1758_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1754_, v_x_3535__boxed_1757_, v_x_1756_);
lean_dec(v_x_1756_);
lean_dec_ref(v_x_1754_);
v_r_1759_ = lean_box(v_res_1758_);
return v_r_1759_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
uint64_t v___x_1762_; size_t v___x_1763_; uint8_t v___x_1764_; 
v___x_1762_ = l_Lean_instHashableMVarId_hash(v_x_1761_);
v___x_1763_ = lean_uint64_to_usize(v___x_1762_);
v___x_1764_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1760_, v___x_1763_, v_x_1761_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
uint8_t v_res_1767_; lean_object* v_r_1768_; 
v_res_1767_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1765_, v_x_1766_);
lean_dec(v_x_1766_);
lean_dec_ref(v_x_1765_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; lean_object* v_mctx_1773_; lean_object* v_eAssignment_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1772_ = lean_st_ref_get(v___y_1770_);
v_mctx_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc_ref(v_mctx_1773_);
lean_dec(v___x_1772_);
v_eAssignment_1774_ = lean_ctor_get(v_mctx_1773_, 8);
lean_inc_ref(v_eAssignment_1774_);
lean_dec_ref(v_mctx_1773_);
v___x_1775_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_1774_, v_mvarId_1769_);
lean_dec_ref(v_eAssignment_1774_);
v___x_1776_ = lean_box(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec(v_mvarId_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(lean_object* v_msg_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_ref_1788_; lean_object* v___x_1789_; lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1798_; 
v_ref_1788_ = lean_ctor_get(v___y_1785_, 2);
v___x_1789_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msg_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1798_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1796_; 
lean_inc(v_ref_1788_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v_ref_1788_);
lean_ctor_set(v___x_1794_, 1, v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 1);
lean_ctor_set(v___x_1792_, 0, v___x_1794_);
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg___boxed(lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1805_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(lean_object* v_x_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
lean_inc(v_x_1811_);
v___x_1822_ = l_Lean_Syntax_isOfKind(v_x_1811_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; 
lean_dec(v_x_1811_);
v___x_1823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v_cfg_1825_; lean_object* v_types_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1824_ = lean_unsigned_to_nat(1u);
v_cfg_1825_ = l_Lean_Syntax_getArg(v_x_1811_, v___x_1824_);
v___x_1901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_1825_);
v___x_1902_ = l_Lean_Syntax_isOfKind(v_cfg_1825_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec(v_cfg_1825_);
lean_dec(v_x_1811_);
v___x_1903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = lean_unsigned_to_nat(2u);
v___x_1905_ = l_Lean_Syntax_getArg(v_x_1811_, v___x_1904_);
lean_dec(v_x_1811_);
v___x_1906_ = l_Lean_Syntax_isNone(v___x_1905_);
if (v___x_1906_ == 0)
{
uint8_t v___x_1907_; 
lean_inc(v___x_1905_);
v___x_1907_ = l_Lean_Syntax_matchesNull(v___x_1905_, v___x_1824_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
lean_dec(v___x_1905_);
lean_dec(v_cfg_1825_);
v___x_1908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; lean_object* v_types_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1909_ = lean_unsigned_to_nat(0u);
v_types_1910_ = l_Lean_Syntax_getArg(v___x_1905_, v___x_1909_);
lean_dec(v___x_1905_);
v___x_1911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_1910_);
v___x_1912_ = l_Lean_Syntax_isOfKind(v_types_1910_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec(v_types_1910_);
lean_dec(v_cfg_1825_);
v___x_1913_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_types_1910_);
v_types_1827_ = v___x_1914_;
v___y_1828_ = v_a_1812_;
v___y_1829_ = v_a_1813_;
v___y_1830_ = v_a_1814_;
v___y_1831_ = v_a_1815_;
v___y_1832_ = v_a_1816_;
v___y_1833_ = v_a_1817_;
v___y_1834_ = v_a_1818_;
v___y_1835_ = v_a_1819_;
goto v___jp_1826_;
}
}
}
else
{
lean_object* v___x_1915_; 
lean_dec(v___x_1905_);
v___x_1915_ = lean_box(0);
v_types_1827_ = v___x_1915_;
v___y_1828_ = v_a_1812_;
v___y_1829_ = v_a_1813_;
v___y_1830_ = v_a_1814_;
v___y_1831_ = v_a_1815_;
v___y_1832_ = v_a_1816_;
v___y_1833_ = v_a_1817_;
v___y_1834_ = v_a_1818_;
v___y_1835_ = v_a_1819_;
goto v___jp_1826_;
}
}
v___jp_1826_:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1899_; 
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1836_, 0);
lean_dec(v_unused_1900_);
v___x_1838_ = v___x_1836_;
v_isShared_1839_ = v_isSharedCheck_1899_;
goto v_resetjp_1837_;
}
else
{
lean_dec(v___x_1836_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1899_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1829_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v_mvarId_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v_mvarId_1842_ = lean_ctor_get(v_a_1841_, 1);
v___x_1843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0));
lean_inc(v_mvarId_1842_);
v___x_1844_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_1825_, v_mvarId_1842_, v___x_1843_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1827_, v_a_1845_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_a_1847_);
v___x_1849_ = v___x_1838_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1847_);
v___x_1849_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_1849_, v_a_1845_, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_a_1841_);
v___f_1853_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1853_, 0, v___x_1852_);
lean_closure_set(v___f_1853_, 1, v___x_1850_);
lean_closure_set(v___f_1853_, 2, v___x_1851_);
v___x_1854_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_1853_, v___y_1828_, v___y_1829_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v_snd_1856_; lean_object* v_target_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_a_1860_; uint8_t v___x_1861_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v_snd_1856_ = lean_ctor_get(v_a_1855_, 1);
lean_inc(v_snd_1856_);
lean_dec(v_a_1855_);
v_target_1857_ = lean_ctor_get(v_snd_1856_, 2);
lean_inc_ref(v_target_1857_);
lean_dec(v_snd_1856_);
v___x_1858_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1857_);
lean_dec_ref(v_target_1857_);
v___x_1859_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v___x_1858_, v___y_1833_);
lean_dec(v___x_1858_);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = lean_unbox(v_a_1860_);
lean_dec(v_a_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2);
v___x_1863_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v___x_1862_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_box(0);
v___x_1865_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1864_, v___y_1829_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
return v___x_1865_;
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1854_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1854_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_a_1845_);
lean_dec(v_a_1841_);
lean_del_object(v___x_1838_);
v_a_1875_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1846_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1846_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_a_1841_);
lean_del_object(v___x_1838_);
lean_dec(v_types_1827_);
v_a_1883_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1844_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1844_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_del_object(v___x_1838_);
lean_dec(v_types_1827_);
lean_dec(v_cfg_1825_);
v_a_1891_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1840_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1840_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
else
{
lean_dec(v_types_1827_);
lean_dec(v_cfg_1825_);
return v___x_1836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed(lean_object* v_x_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(v_x_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(lean_object* v_mvarId_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1927_, v___y_1933_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(v_mvarId_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v_mvarId_1938_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_object* v_00_u03b1_1949_, lean_object* v_msg_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1950_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___boxed(lean_object* v_00_u03b1_1961_, lean_object* v_msg_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(v_00_u03b1_1961_, v_msg_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1972_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_){
_start:
{
uint8_t v___x_1976_; 
v___x_1976_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1974_, v_x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_){
_start:
{
uint8_t v_res_1980_; lean_object* v_r_1981_; 
v_res_1980_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(v_00_u03b2_1977_, v_x_1978_, v_x_1979_);
lean_dec(v_x_1979_);
lean_dec_ref(v_x_1978_);
v_r_1981_ = lean_box(v_res_1980_);
return v_r_1981_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1982_, lean_object* v_x_1983_, size_t v_x_1984_, lean_object* v_x_1985_){
_start:
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1983_, v_x_1984_, v_x_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
size_t v_x_3932__boxed_1991_; uint8_t v_res_1992_; lean_object* v_r_1993_; 
v_x_3932__boxed_1991_ = lean_unbox_usize(v_x_1989_);
lean_dec(v_x_1989_);
v_res_1992_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_1987_, v_x_1988_, v_x_3932__boxed_1991_, v_x_1990_);
lean_dec(v_x_1990_);
lean_dec_ref(v_x_1988_);
v_r_1993_ = lean_box(v_res_1992_);
return v_r_1993_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1994_, lean_object* v_keys_1995_, lean_object* v_vals_1996_, lean_object* v_heq_1997_, lean_object* v_i_1998_, lean_object* v_k_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1995_, v_i_1998_, v_k_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2001_, lean_object* v_keys_2002_, lean_object* v_vals_2003_, lean_object* v_heq_2004_, lean_object* v_i_2005_, lean_object* v_k_2006_){
_start:
{
uint8_t v_res_2007_; lean_object* v_r_2008_; 
v_res_2007_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2001_, v_keys_2002_, v_vals_2003_, v_heq_2004_, v_i_2005_, v_k_2006_);
lean_dec(v_k_2006_);
lean_dec_ref(v_vals_2003_);
lean_dec_ref(v_keys_2002_);
v_r_2008_ = lean_box(v_res_2007_);
return v_r_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2014_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_2016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1));
v___x_2017_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed), 10, 0);
v___x_2018_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2014_, v___x_2015_, v___x_2016_, v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___boxed(lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
return v_res_2020_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(lean_object* v_msg_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_4324__overap_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0);
v___x_4324__overap_2035_ = lean_panic_fn_borrowed(v___x_2034_, v_msg_2022_);
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2031_);
lean_inc(v___y_2030_);
lean_inc_ref(v___y_2029_);
lean_inc(v___y_2028_);
lean_inc_ref(v___y_2027_);
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc(v___y_2023_);
v___x_2036_ = lean_apply_11(v___x_4324__overap_2035_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, lean_box(0));
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___boxed(lean_object* v_msg_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v_msg_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
return v_res_2049_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2));
v___x_2054_ = lean_unsigned_to_nat(46u);
v___x_2055_ = lean_unsigned_to_nat(113u);
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1));
v___x_2057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0));
v___x_2058_ = l_mkPanicMessageWithDecl(v___x_2057_, v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(lean_object* v_a_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2071_ = lean_st_ref_get(v___y_2060_);
v___x_2072_ = lean_box(1);
v___x_2073_ = lean_box(0);
v___x_2074_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2072_, v_a_2059_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2071_);
v___x_2076_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_2077_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_2078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_2079_ = 0;
v___x_2080_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__8);
v___x_2081_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2076_);
lean_ctor_set(v___x_2081_, 1, v___x_2077_);
lean_ctor_set(v___x_2081_, 2, v___x_2075_);
lean_ctor_set(v___x_2081_, 3, v___x_2078_);
lean_ctor_set(v___x_2081_, 4, v___x_2080_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*5, v___x_2079_);
v___x_2082_ = lean_st_mk_ref(v___x_2081_);
v___x_2083_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2073_, v___x_2074_, v___x_2082_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec_ref(v___x_2074_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2097_; 
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; 
v_unused_2098_ = lean_ctor_get(v___x_2083_, 0);
lean_dec(v_unused_2098_);
v___x_2085_ = v___x_2083_;
v_isShared_2086_ = v_isSharedCheck_2097_;
goto v_resetjp_2084_;
}
else
{
lean_dec(v___x_2083_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2097_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v_target_2088_; 
v___x_2087_ = lean_st_ref_get(v___x_2082_);
lean_dec(v___x_2082_);
v_target_2088_ = lean_ctor_get(v___x_2087_, 2);
lean_inc_ref(v_target_2088_);
lean_dec(v___x_2087_);
if (lean_obj_tag(v_target_2088_) == 2)
{
lean_object* v_goal_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v_goal_2089_ = lean_ctor_get(v_target_2088_, 0);
lean_inc_ref(v_goal_2089_);
lean_dec_ref_known(v_target_2088_, 1);
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_st_ref_swap(v___y_2060_, v_goal_2089_);
lean_dec(v___x_2091_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2090_);
v___x_2093_ = v___x_2085_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_dec_ref(v_target_2088_);
lean_del_object(v___x_2085_);
v___x_2095_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3);
v___x_2096_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v___x_2095_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2096_;
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v___x_2082_);
v_a_2099_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2083_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2083_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed(lean_object* v_a_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(v_a_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec(v___y_2108_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(lean_object* v_x_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
lean_inc(v_x_2130_);
v___x_2139_ = l_Lean_Syntax_isOfKind(v_x_2130_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_dec(v_x_2130_);
v___x_2140_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; lean_object* v_cfg_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2141_ = lean_unsigned_to_nat(1u);
v_cfg_2142_ = l_Lean_Syntax_getArg(v_x_2130_, v___x_2141_);
lean_dec(v_x_2130_);
v___x_2143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_2142_);
v___x_2144_ = l_Lean_Syntax_isOfKind(v_cfg_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_dec(v_cfg_2142_);
v___x_2145_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2146_, 1);
v___x_2147_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v_mvarId_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v_mvarId_2149_ = lean_ctor_get(v_a_2148_, 1);
lean_inc(v_mvarId_2149_);
lean_dec(v_a_2148_);
v___x_2150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3));
v___x_2151_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_2142_, v_mvarId_2149_, v___x_2150_, v_a_2135_, v_a_2136_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___f_2153_; lean_object* v___x_2154_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___f_2153_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2153_, 0, v_a_2152_);
v___x_2154_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___f_2153_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
return v___x_2154_;
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
v_a_2155_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2151_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2151_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_cfg_2142_);
v_a_2163_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2147_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2147_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_dec(v_cfg_2142_);
return v___x_2146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___boxed(lean_object* v_x_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(lean_object* v_x_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2180_, v_a_2181_, v_a_2182_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed(lean_object* v_x_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(v_x_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1(){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2207_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2208_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
v___x_2209_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1));
v___x_2210_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed), 10, 0);
v___x_2211_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2207_, v___x_2208_, v___x_2209_, v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___boxed(lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
return v_res_2213_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_BVDecide(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_BVDecide_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_BVDecide(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_BVDecide(builtin);
}
#ifdef __cplusplus
}
#endif
