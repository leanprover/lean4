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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 16, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(64) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(lean_object* v_cfg_8_, lean_object* v_goal_9_, lean_object* v_elaborator_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_14_ = 1;
v___x_15_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___closed__0));
v___x_16_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_16_, 0, v_elaborator_10_);
lean_ctor_set_uint8(v___x_16_, sizeof(void*)*1, v___x_14_);
v___x_17_ = lean_box(0);
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v_goal_9_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
v___x_19_ = lean_st_mk_ref(v___x_18_);
v___x_20_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(v_cfg_8_, v___x_15_, v___x_14_, v___x_16_, v_a_11_, v_a_12_);
lean_dec_ref_known(v___x_16_, 1);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_29_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_29_ == 0)
{
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_29_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_27_; 
v___x_25_ = lean_st_ref_get(v___x_19_);
lean_dec(v___x_19_);
lean_dec(v___x_25_);
if (v_isShared_24_ == 0)
{
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_21_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_dec(v___x_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_8_ = stack[0].m_obj;
lean_object* v_goal_9_ = stack[1].m_obj;
lean_object* v_elaborator_10_ = stack[2].m_obj;
lean_object* v_a_11_ = stack[3].m_obj;
lean_object* v_a_12_ = stack[4].m_obj;
lean_object* v_res_30_;
v_res_30_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_8_, v_goal_9_, v_elaborator_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_30_;
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
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(lean_object* v_cfg_38_, lean_object* v_goal_39_, lean_object* v_elaborator_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_38_, v_goal_39_, v_elaborator_40_, v_a_45_, v_a_46_);
return v___x_48_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_38_ = stack[0].m_obj;
lean_object* v_goal_39_ = stack[1].m_obj;
lean_object* v_elaborator_40_ = stack[2].m_obj;
lean_object* v_a_41_ = stack[3].m_obj;
lean_object* v_a_42_ = stack[4].m_obj;
lean_object* v_a_43_ = stack[5].m_obj;
lean_object* v_a_44_ = stack[6].m_obj;
lean_object* v_a_45_ = stack[7].m_obj;
lean_object* v_a_46_ = stack[8].m_obj;
lean_object* v_res_49_;
v_res_49_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(v_cfg_38_, v_goal_39_, v_elaborator_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___boxed(lean_object* v_cfg_50_, lean_object* v_goal_51_, lean_object* v_elaborator_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(v_cfg_50_, v_goal_51_, v_elaborator_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
return v_res_60_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_box(0);
v___x_62_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
return v___x_63_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0);
v___x_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_67_;
v_res_67_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v_res_69_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_object* v_00_u03b1_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_80_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_71_ = stack[1].m_obj;
lean_object* v___y_72_ = stack[2].m_obj;
lean_object* v___y_73_ = stack[3].m_obj;
lean_object* v___y_74_ = stack[4].m_obj;
lean_object* v___y_75_ = stack[5].m_obj;
lean_object* v___y_76_ = stack[6].m_obj;
lean_object* v___y_77_ = stack[7].m_obj;
lean_object* v___y_78_ = stack[8].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_box(0), v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(v_00_u03b1_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_92_;
}
}
lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_93_, lean_object* v_ref_94_, lean_object* v_a_x3f_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_io_remove_file(v_snd_93_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec(v_ref_94_);
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_117_; 
v_a_106_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_117_ == 0)
{
v___x_108_ = v___x_97_;
v_isShared_109_ = v_isSharedCheck_117_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_97_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_117_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_110_ = lean_io_error_to_string(v_a_106_);
v___x_111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
v___x_112_ = l_Lean_MessageData_ofFormat(v___x_111_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_ref_94_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_113_);
v___x_115_ = v___x_108_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_93_ = stack[0].m_obj;
lean_object* v_ref_94_ = stack[1].m_obj;
lean_object* v_a_x3f_95_ = stack[2].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_93_, v_ref_94_, v_a_x3f_95_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_119_, lean_object* v_ref_120_, lean_object* v_a_x3f_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_119_, v_ref_120_, v_a_x3f_121_);
lean_dec(v_a_x3f_121_);
lean_dec_ref(v_snd_119_);
return v_res_123_;
}
}
lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(lean_object* v_f_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_ref_134_; lean_object* v___x_135_; 
v_ref_134_ = lean_ctor_get(v___y_131_, 2);
v___x_135_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v_fst_137_; lean_object* v_snd_138_; lean_object* v_r_139_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v_fst_137_ = lean_ctor_get(v_a_136_, 0);
lean_inc(v_fst_137_);
v_snd_138_ = lean_ctor_get(v_a_136_, 1);
lean_inc_n(v_snd_138_, 2);
lean_dec(v_a_136_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
v_r_139_ = lean_apply_11(v_f_124_, v_fst_137_, v_snd_138_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
if (lean_obj_tag(v_r_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_164_; 
v_a_140_ = lean_ctor_get(v_r_139_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_r_139_);
if (v_isSharedCheck_164_ == 0)
{
v___x_142_ = v_r_139_;
v_isShared_143_ = v_isSharedCheck_164_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v_r_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_164_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
lean_inc(v_a_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set_tag(v___x_142_, 1);
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_163_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; 
lean_inc(v_ref_134_);
v___x_146_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_138_, v_ref_134_, v___x_145_);
lean_dec_ref(v___x_145_);
lean_dec(v_snd_138_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v___x_146_, 0);
lean_dec(v_unused_154_);
v___x_148_ = v___x_146_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_dec(v___x_146_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v_a_140_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_140_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec(v_a_140_);
v_a_155_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_146_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_146_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_a_165_ = lean_ctor_get(v_r_139_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v_r_139_, 1);
v___x_166_ = lean_box(0);
lean_inc(v_ref_134_);
v___x_167_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_138_, v_ref_134_, v___x_166_);
lean_dec(v_snd_138_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v___x_167_, 0);
lean_dec(v_unused_175_);
v___x_169_ = v___x_167_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_dec(v___x_167_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 1);
lean_ctor_set(v___x_169_, 0, v_a_165_);
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_165_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_165_);
v_a_176_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_167_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_167_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v_f_124_);
v_a_184_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_195_ == 0)
{
v___x_186_ = v___x_135_;
v_isShared_187_ = v_isSharedCheck_195_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_135_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_195_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_188_ = lean_io_error_to_string(v_a_184_);
v___x_189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___x_190_ = l_Lean_MessageData_ofFormat(v___x_189_);
lean_inc(v_ref_134_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v_ref_134_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_191_);
v___x_193_ = v___x_186_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_124_ = stack[0].m_obj;
lean_object* v___y_125_ = stack[1].m_obj;
lean_object* v___y_126_ = stack[2].m_obj;
lean_object* v___y_127_ = stack[3].m_obj;
lean_object* v___y_128_ = stack[4].m_obj;
lean_object* v___y_129_ = stack[5].m_obj;
lean_object* v___y_130_ = stack[6].m_obj;
lean_object* v___y_131_ = stack[7].m_obj;
lean_object* v___y_132_ = stack[8].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
return v_res_207_;
}
}
lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(lean_object* v_00_u03b1_208_, lean_object* v_f_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
return v___x_219_;
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_209_ = stack[1].m_obj;
lean_object* v___y_210_ = stack[2].m_obj;
lean_object* v___y_211_ = stack[3].m_obj;
lean_object* v___y_212_ = stack[4].m_obj;
lean_object* v___y_213_ = stack[5].m_obj;
lean_object* v___y_214_ = stack[6].m_obj;
lean_object* v___y_215_ = stack[7].m_obj;
lean_object* v___y_216_ = stack[8].m_obj;
lean_object* v___y_217_ = stack[9].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(lean_box(0), v_f_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_221_, lean_object* v_f_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(v_00_u03b1_221_, v_f_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_232_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_x_236_, lean_object* v_lratFile_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_237_, v_a_233_, v_a_234_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v_a_235_);
v___x_250_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_250_, 0, v___x_249_);
lean_closure_set(v___x_250_, 1, v_a_248_);
v___x_251_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_250_, v___y_238_, v___y_239_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref_known(v___x_251_, 1);
v___x_252_ = lean_box(0);
v___x_253_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_252_, v___y_239_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
return v___x_253_;
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_251_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_251_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref(v_a_235_);
v_a_262_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_247_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_247_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_233_ = stack[0].m_obj;
lean_object* v_a_234_ = stack[1].m_obj;
lean_object* v_a_235_ = stack[2].m_obj;
lean_object* v_x_236_ = stack[3].m_obj;
lean_object* v_lratFile_237_ = stack[4].m_obj;
lean_object* v___y_238_ = stack[5].m_obj;
lean_object* v___y_239_ = stack[6].m_obj;
lean_object* v___y_240_ = stack[7].m_obj;
lean_object* v___y_241_ = stack[8].m_obj;
lean_object* v___y_242_ = stack[9].m_obj;
lean_object* v___y_243_ = stack[10].m_obj;
lean_object* v___y_244_ = stack[11].m_obj;
lean_object* v___y_245_ = stack[12].m_obj;
lean_object* v_res_270_;
v_res_270_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(v_a_233_, v_a_234_, v_a_235_, v_x_236_, v_lratFile_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed(lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_x_274_, lean_object* v_lratFile_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(v_a_271_, v_a_272_, v_a_273_, v_x_274_, v_lratFile_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v_x_274_);
return v_res_285_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(lean_object* v_x_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
lean_inc(v_x_312_);
v___x_323_ = l_Lean_Syntax_isOfKind(v_x_312_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_x_312_);
v___x_324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v_cfg_326_; lean_object* v_types_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v_cfg_326_ = l_Lean_Syntax_getArg(v_x_312_, v___x_325_);
v___x_372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_326_);
v___x_373_ = l_Lean_Syntax_isOfKind(v_cfg_326_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_cfg_326_);
lean_dec(v_x_312_);
v___x_374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_374_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(2u);
v___x_376_ = l_Lean_Syntax_getArg(v_x_312_, v___x_375_);
lean_dec(v_x_312_);
v___x_377_ = l_Lean_Syntax_isNone(v___x_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
lean_inc(v___x_376_);
v___x_378_ = l_Lean_Syntax_matchesNull(v___x_376_, v___x_325_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v___x_376_);
lean_dec(v_cfg_326_);
v___x_379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v_types_381_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v_types_381_ = l_Lean_Syntax_getArg(v___x_376_, v___x_380_);
lean_dec(v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_381_);
v___x_385_ = l_Lean_Syntax_isOfKind(v_types_381_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v_types_381_);
lean_dec(v_cfg_326_);
v___x_386_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_386_;
}
else
{
goto v___jp_382_;
}
}
else
{
goto v___jp_382_;
}
v___jp_382_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v_types_381_);
v_types_328_ = v___x_383_;
v___y_329_ = v_a_313_;
v___y_330_ = v_a_314_;
v___y_331_ = v_a_315_;
v___y_332_ = v_a_316_;
v___y_333_ = v_a_317_;
v___y_334_ = v_a_318_;
v___y_335_ = v_a_319_;
v___y_336_ = v_a_320_;
goto v___jp_327_;
}
}
}
else
{
lean_object* v___x_387_; 
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_types_328_ = v___x_387_;
v___y_329_ = v_a_313_;
v___y_330_ = v_a_314_;
v___y_331_ = v_a_315_;
v___y_332_ = v_a_316_;
v___y_333_ = v_a_317_;
v___y_334_ = v_a_318_;
v___y_335_ = v_a_319_;
v___y_336_ = v_a_320_;
goto v___jp_327_;
}
}
v___jp_327_:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v___x_338_; 
lean_dec_ref_known(v___x_337_, 1);
v___x_338_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_330_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v_mvarId_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v_mvarId_340_ = lean_ctor_get(v_a_339_, 1);
v___x_341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7));
lean_inc(v_mvarId_340_);
v___x_342_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_326_, v_mvarId_340_, v___x_341_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_328_, v_a_343_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___f_346_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed), 14, 3);
lean_closure_set(v___f_346_, 0, v_a_343_);
lean_closure_set(v___f_346_, 1, v_a_345_);
lean_closure_set(v___f_346_, 2, v_a_339_);
v___x_347_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v___f_346_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
return v___x_347_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_a_343_);
lean_dec(v_a_339_);
v_a_348_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_344_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_344_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_a_339_);
lean_dec(v_types_328_);
v_a_356_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_342_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_342_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_types_328_);
lean_dec(v_cfg_326_);
v_a_364_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_338_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_338_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_dec(v_types_328_);
lean_dec(v_cfg_326_);
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_312_ = stack[0].m_obj;
lean_object* v_a_313_ = stack[1].m_obj;
lean_object* v_a_314_ = stack[2].m_obj;
lean_object* v_a_315_ = stack[3].m_obj;
lean_object* v_a_316_ = stack[4].m_obj;
lean_object* v_a_317_ = stack[5].m_obj;
lean_object* v_a_318_ = stack[6].m_obj;
lean_object* v_a_319_ = stack[7].m_obj;
lean_object* v_a_320_ = stack[8].m_obj;
lean_object* v_res_388_;
v_res_388_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(v_x_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed(lean_object* v_x_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(v_x_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
return v_res_399_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1(){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__15));
v___x_444_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___boxed), 10, 0);
v___x_445_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_441_, v___x_442_, v___x_443_, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_446_;
v_res_446_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___boxed(lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1();
return v_res_448_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; 
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
v___x_459_ = lean_apply_9(v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, lean_box(0));
return v___x_459_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_449_ = stack[0].m_obj;
lean_object* v___y_450_ = stack[1].m_obj;
lean_object* v___y_451_ = stack[2].m_obj;
lean_object* v___y_452_ = stack[3].m_obj;
lean_object* v___y_453_ = stack[4].m_obj;
lean_object* v___y_454_ = stack[5].m_obj;
lean_object* v___y_455_ = stack[6].m_obj;
lean_object* v___y_456_ = stack[7].m_obj;
lean_object* v___y_457_ = stack[8].m_obj;
lean_object* v_res_460_;
v_res_460_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(v_x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed(lean_object* v_x_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0(v_x_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_471_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(lean_object* v_mvarId_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; 
lean_inc(v___y_477_);
lean_inc_ref(v___y_476_);
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_483_, 0, v_x_473_);
lean_closure_set(v___f_483_, 1, v___y_474_);
lean_closure_set(v___f_483_, 2, v___y_475_);
lean_closure_set(v___f_483_, 3, v___y_476_);
lean_closure_set(v___f_483_, 4, v___y_477_);
v___x_484_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_472_, v___f_483_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_484_) == 0)
{
return v___x_484_;
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_472_ = stack[0].m_obj;
lean_object* v_x_473_ = stack[1].m_obj;
lean_object* v___y_474_ = stack[2].m_obj;
lean_object* v___y_475_ = stack[3].m_obj;
lean_object* v___y_476_ = stack[4].m_obj;
lean_object* v___y_477_ = stack[5].m_obj;
lean_object* v___y_478_ = stack[6].m_obj;
lean_object* v___y_479_ = stack[7].m_obj;
lean_object* v___y_480_ = stack[8].m_obj;
lean_object* v___y_481_ = stack[9].m_obj;
lean_object* v_res_493_;
v_res_493_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_472_, v_x_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg___boxed(lean_object* v_mvarId_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_494_, v_x_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_505_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(lean_object* v_00_u03b1_506_, lean_object* v_mvarId_507_, lean_object* v_x_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_507_, v_x_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_518_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_507_ = stack[1].m_obj;
lean_object* v_x_508_ = stack[2].m_obj;
lean_object* v___y_509_ = stack[3].m_obj;
lean_object* v___y_510_ = stack[4].m_obj;
lean_object* v___y_511_ = stack[5].m_obj;
lean_object* v___y_512_ = stack[6].m_obj;
lean_object* v___y_513_ = stack[7].m_obj;
lean_object* v___y_514_ = stack[8].m_obj;
lean_object* v___y_515_ = stack[9].m_obj;
lean_object* v___y_516_ = stack[10].m_obj;
lean_object* v_res_519_;
v_res_519_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(lean_box(0), v_mvarId_507_, v_x_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
stack->m_obj
 = v_res_519_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___boxed(lean_object* v_00_u03b1_520_, lean_object* v_mvarId_521_, lean_object* v_x_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1(v_00_u03b1_520_, v_mvarId_521_, v_x_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_532_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Array_mkArray0___redArg();
return v___x_543_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(size_t v_sz_544_, size_t v_i_545_, lean_object* v_bs_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_bs_546_);
return v___x_550_;
}
else
{
lean_object* v_ref_551_; lean_object* v_v_552_; lean_object* v___x_553_; lean_object* v_bs_x27_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; 
v_ref_551_ = lean_ctor_get(v___y_547_, 2);
v_v_552_ = lean_array_uget(v_bs_546_, v_i_545_);
v___x_553_ = lean_unsigned_to_nat(0u);
v_bs_x27_554_ = lean_array_uset(v_bs_546_, v_i_545_, v___x_553_);
v___x_555_ = 0;
v___x_556_ = l_Lean_SourceInfo_fromRef(v_ref_551_, v___x_555_);
v___x_557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__1));
v___x_558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_559_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
lean_inc(v___x_556_);
v___x_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_560_, 0, v___x_556_);
lean_ctor_set(v___x_560_, 1, v___x_558_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
v___x_561_ = l_Lean_Syntax_node2(v___x_556_, v___x_557_, v_v_552_, v___x_560_);
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_add(v_i_545_, v___x_562_);
v___x_564_ = lean_array_uset(v_bs_x27_554_, v_i_545_, v___x_561_);
v_i_545_ = v___x_563_;
v_bs_546_ = v___x_564_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_544_ = stack[0].m_num;
size_t v_i_545_ = stack[1].m_num;
lean_object* v_bs_546_ = stack[2].m_obj;
lean_object* v___y_547_ = stack[3].m_obj;
lean_object* v_res_566_;
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_544_, v_i_545_, v_bs_546_, v___y_547_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___boxed(lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_bs_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_573_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_boxed_572_, v_i_boxed_573_, v_bs_569_, v___y_570_);
lean_dec_ref(v___y_570_);
return v_res_574_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(lean_object* v_a_578_, size_t v___x_579_, lean_object* v___x_580_, lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v___x_583_, lean_object* v_final_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___x_590_; size_t v_sz_591_; lean_object* v___x_592_; 
v___x_590_ = lean_array_push(v_a_578_, v_final_584_);
v_sz_591_ = lean_array_size(v___x_590_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_591_, v___x_579_, v___x_590_, v___y_587_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_615_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_615_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_615_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_615_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_ref_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v_ref_597_ = lean_ctor_get(v___y_587_, 2);
v___x_598_ = 0;
v___x_599_ = l_Lean_SourceInfo_fromRef(v_ref_597_, v___x_598_);
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__0));
lean_inc_ref(v___x_583_);
lean_inc_ref(v___x_582_);
lean_inc_ref(v___x_581_);
lean_inc_ref(v___x_580_);
v___x_601_ = l_Lean_Name_mkStr5(v___x_580_, v___x_581_, v___x_582_, v___x_583_, v___x_600_);
v___x_602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__1));
v___x_603_ = l_Lean_Name_mkStr5(v___x_580_, v___x_581_, v___x_582_, v___x_583_, v___x_602_);
v___x_604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_605_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
v___x_607_ = l_Lean_Syntax_SepArray_ofElems(v___x_606_, v_a_593_);
lean_dec(v_a_593_);
v___x_608_ = l_Array_append___redArg(v___x_605_, v___x_607_);
lean_dec_ref(v___x_607_);
lean_inc_n(v___x_599_, 2);
v___x_609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_609_, 0, v___x_599_);
lean_ctor_set(v___x_609_, 1, v___x_604_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
v___x_610_ = l_Lean_Syntax_node1(v___x_599_, v___x_603_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node1(v___x_599_, v___x_601_, v___x_610_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_611_);
v___x_613_ = v___x_595_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v___x_583_);
lean_dec_ref(v___x_582_);
lean_dec_ref(v___x_581_);
lean_dec_ref(v___x_580_);
v_a_616_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_592_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_592_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_578_ = stack[0].m_obj;
size_t v___x_579_ = stack[1].m_num;
lean_object* v___x_580_ = stack[2].m_obj;
lean_object* v___x_581_ = stack[3].m_obj;
lean_object* v___x_582_ = stack[4].m_obj;
lean_object* v___x_583_ = stack[5].m_obj;
lean_object* v_final_584_ = stack[6].m_obj;
lean_object* v___y_585_ = stack[7].m_obj;
lean_object* v___y_586_ = stack[8].m_obj;
lean_object* v___y_587_ = stack[9].m_obj;
lean_object* v___y_588_ = stack[10].m_obj;
lean_object* v_res_624_;
v_res_624_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(v_a_578_, v___x_579_, v___x_580_, v___x_581_, v___x_582_, v___x_583_, v_final_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed(lean_object* v_a_625_, lean_object* v___x_626_, lean_object* v___x_627_, lean_object* v___x_628_, lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v_final_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
size_t v___x_27161__boxed_637_; lean_object* v_res_638_; 
v___x_27161__boxed_637_ = lean_unbox_usize(v___x_626_);
lean_dec(v___x_626_);
v_res_638_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(v_a_625_, v___x_27161__boxed_637_, v___x_627_, v___x_628_, v___x_629_, v___x_630_, v_final_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_638_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
v___x_677_ = l_String_toRawSubstring_x27(v___x_676_);
return v___x_677_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(size_t v_sz_713_, size_t v_i_714_, lean_object* v_bs_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_714_, v_sz_713_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_bs_715_);
return v___x_722_;
}
else
{
lean_object* v_v_723_; lean_object* v_hyp_724_; lean_object* v_grindProof_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_823_; 
v_v_723_ = lean_array_uget(v_bs_715_, v_i_714_);
v_hyp_724_ = lean_ctor_get(v_v_723_, 0);
v_grindProof_725_ = lean_ctor_get(v_v_723_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_v_723_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_v_723_, 1);
lean_dec(v_unused_824_);
v___x_727_ = v_v_723_;
v_isShared_728_ = v_isSharedCheck_823_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_grindProof_725_);
lean_inc(v_hyp_724_);
lean_dec(v_v_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_823_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_type_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_819_; 
v_type_729_ = lean_ctor_get(v_hyp_724_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_hyp_724_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; 
v_unused_820_ = lean_ctor_get(v_hyp_724_, 3);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_hyp_724_, 2);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_hyp_724_, 0);
lean_dec(v_unused_822_);
v___x_731_ = v_hyp_724_;
v_isShared_732_ = v_isSharedCheck_819_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_type_729_);
lean_dec(v_hyp_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_819_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v_bs_x27_734_; lean_object* v_a_736_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v_bs_x27_734_ = lean_array_uset(v_bs_715_, v_i_714_, v___x_733_);
v___x_741_ = lean_box(1);
v___x_742_ = l_Lean_PrettyPrinter_delab(v_type_729_, v___x_741_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
v___x_744_ = lean_apply_5(v_grindProof_725_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
if (lean_obj_tag(v_a_745_) == 0)
{
lean_object* v_ref_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_del_object(v___x_731_);
v_ref_746_ = lean_ctor_get(v___y_718_, 2);
v___x_747_ = 0;
v___x_748_ = l_Lean_SourceInfo_fromRef(v_ref_746_, v___x_747_);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1));
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
lean_inc_n(v___x_748_, 2);
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_748_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_753_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 1);
lean_ctor_set(v___x_727_, 2, v___x_753_);
lean_ctor_set(v___x_727_, 1, v___x_752_);
lean_ctor_set(v___x_727_, 0, v___x_748_);
v___x_755_ = v___x_727_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v___x_753_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
lean_inc(v___x_748_);
v___x_757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_748_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_Syntax_node4(v___x_748_, v___x_749_, v___x_751_, v___x_755_, v___x_757_, v_a_743_);
v_a_736_ = v___x_758_;
goto v___jp_735_;
}
}
else
{
lean_object* v_toCold_760_; lean_object* v_val_761_; lean_object* v_ref_762_; lean_object* v_quotContext_763_; lean_object* v_currMacroScope_764_; uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v_toCold_760_ = lean_ctor_get(v___y_718_, 0);
v_val_761_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v_a_745_, 1);
v_ref_762_ = lean_ctor_get(v___y_718_, 2);
v_quotContext_763_ = lean_ctor_get(v_toCold_760_, 8);
v_currMacroScope_764_ = lean_ctor_get(v_toCold_760_, 9);
v___x_765_ = 0;
v___x_766_ = l_Lean_SourceInfo_fromRef(v_ref_762_, v___x_765_);
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
v___x_768_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4));
lean_inc_n(v___x_766_, 2);
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_766_);
lean_ctor_set(v___x_769_, 1, v___x_767_);
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7));
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9));
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11));
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13));
v___x_774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14);
v___x_775_ = lean_box(0);
lean_inc(v_currMacroScope_764_);
lean_inc(v_quotContext_763_);
v___x_776_ = l_Lean_addMacroScope(v_quotContext_763_, v___x_775_, v_currMacroScope_764_);
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21));
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 3);
lean_ctor_set(v___x_731_, 3, v___x_777_);
lean_ctor_set(v___x_731_, 2, v___x_776_);
lean_ctor_set(v___x_731_, 1, v___x_774_);
lean_ctor_set(v___x_731_, 0, v___x_766_);
v___x_779_ = v___x_731_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v___x_777_);
v___x_779_ = v_reuseFailAlloc_801_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
lean_inc_n(v___x_766_, 3);
v___x_780_ = l_Lean_Syntax_node1(v___x_766_, v___x_773_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node1(v___x_766_, v___x_772_, v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 1);
lean_ctor_set(v___x_727_, 2, v___x_783_);
lean_ctor_set(v___x_727_, 1, v___x_782_);
lean_ctor_set(v___x_727_, 0, v___x_766_);
v___x_785_ = v___x_727_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v___x_783_);
v___x_785_ = v_reuseFailAlloc_800_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23));
v___x_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
lean_inc_n(v___x_766_, 8);
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_766_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v___x_766_, v___x_786_, v___x_788_, v_a_743_);
v___x_790_ = l_Lean_Syntax_node1(v___x_766_, v___x_782_, v___x_789_);
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24));
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_766_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26));
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27));
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_766_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_Syntax_node2(v___x_766_, v___x_793_, v___x_795_, v_val_761_);
v___x_797_ = l_Lean_Syntax_node5(v___x_766_, v___x_771_, v___x_781_, v___x_785_, v___x_790_, v___x_792_, v___x_796_);
v___x_798_ = l_Lean_Syntax_node1(v___x_766_, v___x_770_, v___x_797_);
v___x_799_ = l_Lean_Syntax_node2(v___x_766_, v___x_768_, v___x_769_, v___x_798_);
v_a_736_ = v___x_799_;
goto v___jp_735_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_a_743_);
lean_dec_ref(v_bs_x27_734_);
lean_del_object(v___x_731_);
lean_del_object(v___x_727_);
v_a_802_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_744_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_744_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_del_object(v___x_731_);
lean_del_object(v___x_727_);
lean_dec_ref(v_grindProof_725_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_810_; 
v_a_810_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_742_, 1);
v_a_736_ = v_a_810_;
goto v___jp_735_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_bs_x27_734_);
v_a_811_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_742_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_742_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
v___jp_735_:
{
size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_714_, v___x_737_);
v___x_739_ = lean_array_uset(v_bs_x27_734_, v_i_714_, v_a_736_);
v_i_714_ = v___x_738_;
v_bs_715_ = v___x_739_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_713_ = stack[0].m_num;
size_t v_i_714_ = stack[1].m_num;
lean_object* v_bs_715_ = stack[2].m_obj;
lean_object* v___y_716_ = stack[3].m_obj;
lean_object* v___y_717_ = stack[4].m_obj;
lean_object* v___y_718_ = stack[5].m_obj;
lean_object* v___y_719_ = stack[6].m_obj;
lean_object* v_res_825_;
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_713_, v_i_714_, v_bs_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___boxed(lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_bs_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
size_t v_sz_boxed_834_; size_t v_i_boxed_835_; lean_object* v_res_836_; 
v_sz_boxed_834_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_835_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_boxed_834_, v_i_boxed_835_, v_bs_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
return v_res_836_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(size_t v_sz_837_, size_t v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_837_, v_i_838_, v_bs_839_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
return v___x_849_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_837_ = stack[0].m_num;
size_t v_i_838_ = stack[1].m_num;
lean_object* v_bs_839_ = stack[2].m_obj;
lean_object* v___y_840_ = stack[3].m_obj;
lean_object* v___y_841_ = stack[4].m_obj;
lean_object* v___y_842_ = stack[5].m_obj;
lean_object* v___y_843_ = stack[6].m_obj;
lean_object* v___y_844_ = stack[7].m_obj;
lean_object* v___y_845_ = stack[8].m_obj;
lean_object* v___y_846_ = stack[9].m_obj;
lean_object* v___y_847_ = stack[10].m_obj;
lean_object* v_res_850_;
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(v_sz_837_, v_i_838_, v_bs_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed(lean_object* v_sz_851_, lean_object* v_i_852_, lean_object* v_bs_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
size_t v_sz_boxed_863_; size_t v_i_boxed_864_; lean_object* v_res_865_; 
v_sz_boxed_863_ = lean_unbox_usize(v_sz_851_);
lean_dec(v_sz_851_);
v_i_boxed_864_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_res_865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(v_sz_boxed_863_, v_i_boxed_864_, v_bs_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_865_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object* v_x_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
lean_inc(v_x_903_);
v___x_926_ = l_Lean_Syntax_isOfKind(v_x_903_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; 
lean_dec(v_x_903_);
v___x_927_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v_cfgStx_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_928_ = lean_unsigned_to_nat(1u);
v_cfgStx_929_ = l_Lean_Syntax_getArg(v_x_903_, v___x_928_);
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_929_);
v___x_931_ = l_Lean_Syntax_isOfKind(v_cfgStx_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v_cfgStx_929_);
lean_dec(v_x_903_);
v___x_932_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v_tk_934_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v_typesStx_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v_tk_934_ = l_Lean_Syntax_getArg(v_x_903_, v___x_933_);
v___x_1180_ = lean_unsigned_to_nat(2u);
v___x_1181_ = l_Lean_Syntax_getArg(v_x_903_, v___x_1180_);
lean_dec(v_x_903_);
v___x_1182_ = l_Lean_Syntax_isNone(v___x_1181_);
if (v___x_1182_ == 0)
{
uint8_t v___x_1183_; 
lean_inc(v___x_1181_);
v___x_1183_ = l_Lean_Syntax_matchesNull(v___x_1181_, v___x_928_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
lean_dec(v___x_1181_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v___x_1184_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1184_;
}
else
{
lean_object* v_typesStx_1185_; 
v_typesStx_1185_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_933_);
lean_dec(v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1185_);
v___x_1189_ = l_Lean_Syntax_isOfKind(v_typesStx_1185_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec(v_typesStx_1185_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v___x_1190_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1190_;
}
else
{
goto v___jp_1186_;
}
}
else
{
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_typesStx_1185_);
v_typesStx_1047_ = v___x_1187_;
v___y_1048_ = v_a_904_;
v___y_1049_ = v_a_905_;
v___y_1050_ = v_a_906_;
v___y_1051_ = v_a_907_;
v___y_1052_ = v_a_908_;
v___y_1053_ = v_a_909_;
v___y_1054_ = v_a_910_;
v___y_1055_ = v_a_911_;
goto v___jp_1046_;
}
}
}
else
{
lean_object* v___x_1191_; 
lean_dec(v___x_1181_);
v___x_1191_ = lean_box(0);
v_typesStx_1047_ = v___x_1191_;
v___y_1048_ = v_a_904_;
v___y_1049_ = v_a_905_;
v___y_1050_ = v_a_906_;
v___y_1051_ = v_a_907_;
v___y_1052_ = v_a_908_;
v___y_1053_ = v_a_909_;
v___y_1054_ = v_a_910_;
v___y_1055_ = v_a_911_;
goto v___jp_1046_;
}
v___jp_935_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_inc_ref(v___y_938_);
v___x_949_ = l_Array_append___redArg(v___y_938_, v___y_948_);
lean_dec_ref(v___y_948_);
lean_inc(v___y_936_);
lean_inc(v___y_940_);
v___x_950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_950_, 0, v___y_940_);
lean_ctor_set(v___x_950_, 1, v___y_936_);
lean_ctor_set(v___x_950_, 2, v___x_949_);
lean_inc(v___y_941_);
v___x_951_ = l_Lean_Syntax_node3(v___y_940_, v___y_941_, v___y_939_, v_cfgStx_929_, v___x_950_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_946_);
v___x_952_ = lean_apply_6(v___y_937_, v___x_951_, v___y_946_, v___y_942_, v___y_947_, v___y_944_, lean_box(0));
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v_a_953_);
v___x_956_ = lean_box(0);
v___x_957_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
lean_ctor_set(v___x_957_, 2, v___x_956_);
lean_ctor_set(v___x_957_, 3, v___x_956_);
lean_ctor_set(v___x_957_, 4, v___x_956_);
lean_ctor_set(v___x_957_, 5, v___x_956_);
lean_inc(v___y_943_);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___y_943_);
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_960_ = 4;
v___x_961_ = l_Lean_MessageData_nil;
v___x_962_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_934_, v___x_957_, v___x_958_, v___x_959_, v___x_956_, v___x_960_, v___x_961_, v___y_947_, v___y_944_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref_known(v___x_962_, 1);
v___y_914_ = v___y_945_;
v___y_915_ = v___y_946_;
v___y_916_ = v___y_942_;
v___y_917_ = v___y_947_;
v___y_918_ = v___y_944_;
goto v___jp_913_;
}
else
{
return v___x_962_;
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v_tk_934_);
v_a_963_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_952_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_952_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
v___jp_971_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_inc_ref(v___y_977_);
v___x_986_ = l_Array_append___redArg(v___y_977_, v___y_985_);
lean_dec_ref(v___y_985_);
lean_inc(v___y_982_);
lean_inc(v___y_974_);
v___x_987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_987_, 0, v___y_974_);
lean_ctor_set(v___x_987_, 1, v___y_982_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
v___x_988_ = lean_box(2);
v___x_989_ = l_Lean_Syntax_mkStrLit(v___y_983_, v___x_988_);
lean_inc(v___y_972_);
v___x_990_ = l_Lean_Syntax_node4(v___y_974_, v___y_972_, v___y_975_, v_cfgStx_929_, v___x_987_, v___x_989_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_981_);
v___x_991_ = lean_apply_6(v___y_973_, v___x_990_, v___y_981_, v___y_976_, v___y_984_, v___y_979_, lean_box(0));
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_a_992_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
lean_ctor_set(v___x_996_, 3, v___x_995_);
lean_ctor_set(v___x_996_, 4, v___x_995_);
lean_ctor_set(v___x_996_, 5, v___x_995_);
lean_inc(v___y_978_);
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v___y_978_);
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_999_ = 4;
v___x_1000_ = l_Lean_MessageData_nil;
v___x_1001_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_934_, v___x_996_, v___x_997_, v___x_998_, v___x_995_, v___x_999_, v___x_1000_, v___y_984_, v___y_979_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_dec_ref_known(v___x_1001_, 1);
v___y_914_ = v___y_980_;
v___y_915_ = v___y_981_;
v___y_916_ = v___y_976_;
v___y_917_ = v___y_984_;
v___y_918_ = v___y_979_;
goto v___jp_913_;
}
else
{
return v___x_1001_;
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_tk_934_);
v_a_1002_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_991_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_991_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
v___jp_1010_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_inc_ref(v___y_1015_);
v___x_1024_ = l_Array_append___redArg(v___y_1015_, v___y_1023_);
lean_dec_ref(v___y_1023_);
lean_inc(v___y_1020_);
lean_inc(v___y_1013_);
v___x_1025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1025_, 0, v___y_1013_);
lean_ctor_set(v___x_1025_, 1, v___y_1020_);
lean_ctor_set(v___x_1025_, 2, v___x_1024_);
lean_inc(v___y_1014_);
v___x_1026_ = l_Lean_Syntax_node3(v___y_1013_, v___y_1014_, v___y_1011_, v_cfgStx_929_, v___x_1025_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1022_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1021_);
v___x_1027_ = lean_apply_6(v___y_1012_, v___x_1026_, v___y_1021_, v___y_1016_, v___y_1022_, v___y_1018_, lean_box(0));
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_a_1028_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_ctor_set(v___x_1032_, 2, v___x_1031_);
lean_ctor_set(v___x_1032_, 3, v___x_1031_);
lean_ctor_set(v___x_1032_, 4, v___x_1031_);
lean_ctor_set(v___x_1032_, 5, v___x_1031_);
lean_inc(v___y_1017_);
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___y_1017_);
v___x_1034_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1035_ = 4;
v___x_1036_ = l_Lean_MessageData_nil;
v___x_1037_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_934_, v___x_1032_, v___x_1033_, v___x_1034_, v___x_1031_, v___x_1035_, v___x_1036_, v___y_1022_, v___y_1018_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_dec_ref_known(v___x_1037_, 1);
v___y_914_ = v___y_1019_;
v___y_915_ = v___y_1021_;
v___y_916_ = v___y_1016_;
v___y_917_ = v___y_1022_;
v___y_918_ = v___y_1018_;
goto v___jp_913_;
}
else
{
return v___x_1037_;
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_tk_934_);
v_a_1038_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1027_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1027_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
v___jp_1046_:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1178_; 
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v___x_1056_, 0);
lean_dec(v_unused_1179_);
v___x_1058_ = v___x_1056_;
v_isShared_1059_ = v_isSharedCheck_1178_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v___x_1056_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1178_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1049_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v_mvarId_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v_mvarId_1062_ = lean_ctor_get(v_a_1061_, 1);
lean_inc_n(v_mvarId_1062_, 2);
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5));
lean_inc(v_cfgStx_929_);
v___x_1064_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_929_, v_mvarId_1062_, v___x_1063_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
lean_inc(v_typesStx_1047_);
v___x_1066_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1047_, v_a_1065_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1065_, v_a_1067_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
lean_ctor_set(v___x_1058_, 0, v_a_1061_);
v___x_1071_ = v___x_1058_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1061_);
v___x_1071_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed), 12, 2);
lean_closure_set(v___x_1072_, 0, v___x_1071_);
lean_closure_set(v___x_1072_, 1, v_a_1069_);
v___x_1073_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1072_, v___y_1048_, v___y_1049_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v_lemmas_1075_; lean_object* v_action_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1136_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_lemmas_1075_ = lean_ctor_get(v_a_1074_, 0);
v_action_1076_ = lean_ctor_get(v_a_1074_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_a_1074_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1078_ = v_a_1074_;
v_isShared_1079_ = v_isSharedCheck_1136_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_action_1076_);
lean_inc(v_lemmas_1075_);
lean_dec(v_a_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1136_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
size_t v_sz_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_sz_1080_ = lean_array_size(v_lemmas_1075_);
v___x_1081_ = lean_box_usize(v_sz_1080_);
v___x_1082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___x_1083_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed), 12, 3);
lean_closure_set(v___x_1083_, 0, v___x_1081_);
lean_closure_set(v___x_1083_, 1, v___x_1082_);
lean_closure_set(v___x_1083_, 2, v_lemmas_1075_);
v___x_1084_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_1062_, v___x_1083_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___f_1087_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1087_, 0, v_a_1085_);
lean_closure_set(v___f_1087_, 1, v___x_1086_);
lean_closure_set(v___f_1087_, 2, v___x_921_);
lean_closure_set(v___f_1087_, 3, v___x_922_);
lean_closure_set(v___f_1087_, 4, v___x_923_);
lean_closure_set(v___f_1087_, 5, v___x_924_);
switch(lean_obj_tag(v_action_1076_))
{
case 0:
{
lean_object* v_ref_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_ref_1088_ = lean_ctor_get(v___y_1054_, 2);
v___x_1089_ = 0;
v___x_1090_ = l_Lean_SourceInfo_fromRef(v_ref_1088_, v___x_1089_);
v___x_1091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_1092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1090_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 2);
lean_ctor_set(v___x_1078_, 1, v___x_1092_);
lean_ctor_set(v___x_1078_, 0, v___x_1090_);
v___x_1094_ = v___x_1078_;
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
if (lean_obj_tag(v_typesStx_1047_) == 1)
{
lean_object* v_val_1097_; lean_object* v___x_1098_; 
v_val_1097_ = lean_ctor_get(v_typesStx_1047_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_typesStx_1047_, 1);
v___x_1098_ = l_Array_mkArray1___redArg(v_val_1097_);
v___y_1011_ = v___x_1094_;
v___y_1012_ = v___f_1087_;
v___y_1013_ = v___x_1090_;
v___y_1014_ = v___x_1091_;
v___y_1015_ = v___x_1096_;
v___y_1016_ = v___y_1053_;
v___y_1017_ = v_ref_1088_;
v___y_1018_ = v___y_1055_;
v___y_1019_ = v___y_1049_;
v___y_1020_ = v___x_1095_;
v___y_1021_ = v___y_1052_;
v___y_1022_ = v___y_1054_;
v___y_1023_ = v___x_1098_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1099_; 
lean_dec(v_typesStx_1047_);
v___x_1099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_1011_ = v___x_1094_;
v___y_1012_ = v___f_1087_;
v___y_1013_ = v___x_1090_;
v___y_1014_ = v___x_1091_;
v___y_1015_ = v___x_1096_;
v___y_1016_ = v___y_1053_;
v___y_1017_ = v_ref_1088_;
v___y_1018_ = v___y_1055_;
v___y_1019_ = v___y_1049_;
v___y_1020_ = v___x_1095_;
v___y_1021_ = v___y_1052_;
v___y_1022_ = v___y_1054_;
v___y_1023_ = v___x_1099_;
goto v___jp_1010_;
}
}
}
case 1:
{
lean_object* v_path_1101_; lean_object* v_ref_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_path_1101_ = lean_ctor_get(v_action_1076_, 0);
lean_inc_ref(v_path_1101_);
lean_dec_ref_known(v_action_1076_, 1);
v_ref_1102_ = lean_ctor_get(v___y_1054_, 2);
v___x_1103_ = 0;
v___x_1104_ = l_Lean_SourceInfo_fromRef(v_ref_1102_, v___x_1103_);
v___x_1105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12));
lean_inc(v___x_1104_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 2);
lean_ctor_set(v___x_1078_, 1, v___x_1106_);
lean_ctor_set(v___x_1078_, 0, v___x_1104_);
v___x_1108_ = v___x_1078_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1047_) == 1)
{
lean_object* v_val_1111_; lean_object* v___x_1112_; 
v_val_1111_ = lean_ctor_get(v_typesStx_1047_, 0);
lean_inc(v_val_1111_);
lean_dec_ref_known(v_typesStx_1047_, 1);
v___x_1112_ = l_Array_mkArray1___redArg(v_val_1111_);
v___y_972_ = v___x_1105_;
v___y_973_ = v___f_1087_;
v___y_974_ = v___x_1104_;
v___y_975_ = v___x_1108_;
v___y_976_ = v___y_1053_;
v___y_977_ = v___x_1110_;
v___y_978_ = v_ref_1102_;
v___y_979_ = v___y_1055_;
v___y_980_ = v___y_1049_;
v___y_981_ = v___y_1052_;
v___y_982_ = v___x_1109_;
v___y_983_ = v_path_1101_;
v___y_984_ = v___y_1054_;
v___y_985_ = v___x_1112_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1113_; 
lean_dec(v_typesStx_1047_);
v___x_1113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_972_ = v___x_1105_;
v___y_973_ = v___f_1087_;
v___y_974_ = v___x_1104_;
v___y_975_ = v___x_1108_;
v___y_976_ = v___y_1053_;
v___y_977_ = v___x_1110_;
v___y_978_ = v_ref_1102_;
v___y_979_ = v___y_1055_;
v___y_980_ = v___y_1049_;
v___y_981_ = v___y_1052_;
v___y_982_ = v___x_1109_;
v___y_983_ = v_path_1101_;
v___y_984_ = v___y_1054_;
v___y_985_ = v___x_1113_;
goto v___jp_971_;
}
}
}
default: 
{
lean_object* v_ref_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v_ref_1115_ = lean_ctor_get(v___y_1054_, 2);
v___x_1116_ = 0;
v___x_1117_ = l_Lean_SourceInfo_fromRef(v_ref_1115_, v___x_1116_);
v___x_1118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_1119_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6));
lean_inc(v___x_1117_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 2);
lean_ctor_set(v___x_1078_, 1, v___x_1119_);
lean_ctor_set(v___x_1078_, 0, v___x_1117_);
v___x_1121_ = v___x_1078_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1047_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; 
v_val_1124_ = lean_ctor_get(v_typesStx_1047_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v_typesStx_1047_, 1);
v___x_1125_ = l_Array_mkArray1___redArg(v_val_1124_);
v___y_936_ = v___x_1122_;
v___y_937_ = v___f_1087_;
v___y_938_ = v___x_1123_;
v___y_939_ = v___x_1121_;
v___y_940_ = v___x_1117_;
v___y_941_ = v___x_1118_;
v___y_942_ = v___y_1053_;
v___y_943_ = v_ref_1115_;
v___y_944_ = v___y_1055_;
v___y_945_ = v___y_1049_;
v___y_946_ = v___y_1052_;
v___y_947_ = v___y_1054_;
v___y_948_ = v___x_1125_;
goto v___jp_935_;
}
else
{
lean_object* v___x_1126_; 
lean_dec(v_typesStx_1047_);
v___x_1126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_936_ = v___x_1122_;
v___y_937_ = v___f_1087_;
v___y_938_ = v___x_1123_;
v___y_939_ = v___x_1121_;
v___y_940_ = v___x_1117_;
v___y_941_ = v___x_1118_;
v___y_942_ = v___y_1053_;
v___y_943_ = v_ref_1115_;
v___y_944_ = v___y_1055_;
v___y_945_ = v___y_1049_;
v___y_946_ = v___y_1052_;
v___y_947_ = v___y_1054_;
v___y_948_ = v___x_1126_;
goto v___jp_935_;
}
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_del_object(v___x_1078_);
lean_dec(v_action_1076_);
lean_dec(v_typesStx_1047_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v_a_1128_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1084_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1084_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_mvarId_1062_);
lean_dec(v_typesStx_1047_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v_a_1137_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1073_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1073_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_mvarId_1062_);
lean_dec(v_a_1061_);
lean_del_object(v___x_1058_);
lean_dec(v_typesStx_1047_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v_a_1146_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1068_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1068_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_a_1065_);
lean_dec(v_mvarId_1062_);
lean_dec(v_a_1061_);
lean_del_object(v___x_1058_);
lean_dec(v_typesStx_1047_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v_a_1154_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1066_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1066_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_mvarId_1062_);
lean_dec(v_a_1061_);
lean_del_object(v___x_1058_);
lean_dec(v_typesStx_1047_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v_a_1162_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1064_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1064_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_del_object(v___x_1058_);
lean_dec(v_typesStx_1047_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
v_a_1170_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1060_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1060_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1047_);
lean_dec(v_tk_934_);
lean_dec(v_cfgStx_929_);
return v___x_1056_;
}
}
}
}
v___jp_913_:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_box(0);
v___x_920_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_919_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_920_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_903_ = stack[0].m_obj;
lean_object* v_a_904_ = stack[1].m_obj;
lean_object* v_a_905_ = stack[2].m_obj;
lean_object* v_a_906_ = stack[3].m_obj;
lean_object* v_a_907_ = stack[4].m_obj;
lean_object* v_a_908_ = stack[5].m_obj;
lean_object* v_a_909_ = stack[6].m_obj;
lean_object* v_a_910_ = stack[7].m_obj;
lean_object* v_a_911_ = stack[8].m_obj;
lean_object* v_res_1192_;
v_res_1192_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(v_x_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object* v_x_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(v_x_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
return v_res_1203_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_bs_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_1204_, v_i_1205_, v_bs_1206_, v___y_1209_);
return v___x_1212_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1204_ = stack[0].m_num;
size_t v_i_1205_ = stack[1].m_num;
lean_object* v_bs_1206_ = stack[2].m_obj;
lean_object* v___y_1207_ = stack[3].m_obj;
lean_object* v___y_1208_ = stack[4].m_obj;
lean_object* v___y_1209_ = stack[5].m_obj;
lean_object* v___y_1210_ = stack[6].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(v_sz_1204_, v_i_1205_, v_bs_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___boxed(lean_object* v_sz_1214_, lean_object* v_i_1215_, lean_object* v_bs_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
size_t v_sz_boxed_1222_; size_t v_i_boxed_1223_; lean_object* v_res_1224_; 
v_sz_boxed_1222_ = lean_unbox_usize(v_sz_1214_);
lean_dec(v_sz_1214_);
v_i_boxed_1223_ = lean_unbox_usize(v_i_1215_);
lean_dec(v_i_1215_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(v_sz_boxed_1222_, v_i_boxed_1223_, v_bs_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1224_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1(){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1230_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1231_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
v___x_1232_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1));
v___x_1233_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed), 10, 0);
v___x_1234_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1230_, v___x_1231_, v___x_1232_, v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1235_;
v_res_1235_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
stack->m_obj
 = v_res_1235_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___boxed(lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
return v_res_1237_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1238_, lean_object* v_opt_1239_){
_start:
{
lean_object* v_name_1240_; lean_object* v_defValue_1241_; lean_object* v_map_1242_; lean_object* v___x_1243_; 
v_name_1240_ = lean_ctor_get(v_opt_1239_, 0);
v_defValue_1241_ = lean_ctor_get(v_opt_1239_, 1);
v_map_1242_ = lean_ctor_get(v_opts_1238_, 0);
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1242_, v_name_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_unbox(v_defValue_1241_);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; 
v_val_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1245_);
lean_dec_ref_known(v___x_1243_, 1);
if (lean_obj_tag(v_val_1245_) == 1)
{
uint8_t v_v_1246_; 
v_v_1246_ = lean_ctor_get_uint8(v_val_1245_, 0);
lean_dec_ref_known(v_val_1245_, 0);
return v_v_1246_;
}
else
{
uint8_t v___x_1247_; 
lean_dec(v_val_1245_);
v___x_1247_ = lean_unbox(v_defValue_1241_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1238_ = stack[0].m_obj;
lean_object* v_opt_1239_ = stack[1].m_obj;
uint8_t v_res_1248_;
v_res_1248_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v_opts_1238_, v_opt_1239_);
stack->m_num = v_res_1248_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1249_, lean_object* v_opt_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v_opts_1249_, v_opt_1250_);
lean_dec_ref(v_opt_1250_);
lean_dec_ref(v_opts_1249_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1259_, uint8_t v___y_1260_, lean_object* v_x_1261_){
_start:
{
if (lean_obj_tag(v_x_1261_) == 1)
{
lean_object* v_pre_1262_; 
v_pre_1262_ = lean_ctor_get(v_x_1261_, 0);
switch(lean_obj_tag(v_pre_1262_))
{
case 1:
{
lean_object* v_pre_1263_; 
v_pre_1263_ = lean_ctor_get(v_pre_1262_, 0);
switch(lean_obj_tag(v_pre_1263_))
{
case 0:
{
lean_object* v_str_1264_; lean_object* v_str_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_str_1264_ = lean_ctor_get(v_x_1261_, 1);
v_str_1265_ = lean_ctor_get(v_pre_1262_, 1);
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3));
v___x_1267_ = lean_string_dec_eq(v_str_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1269_ = lean_string_dec_eq(v_str_1265_, v___x_1268_);
if (v___x_1269_ == 0)
{
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1271_ = lean_string_dec_eq(v_str_1264_, v___x_1270_);
if (v___x_1271_ == 0)
{
return v___x_1271_;
}
else
{
return v_suppressElabErrors_1259_;
}
}
}
else
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1273_ = lean_string_dec_eq(v_str_1264_, v___x_1272_);
if (v___x_1273_ == 0)
{
return v___x_1273_;
}
else
{
return v_suppressElabErrors_1259_;
}
}
}
case 1:
{
lean_object* v_pre_1274_; 
v_pre_1274_ = lean_ctor_get(v_pre_1263_, 0);
if (lean_obj_tag(v_pre_1274_) == 0)
{
lean_object* v_str_1275_; lean_object* v_str_1276_; lean_object* v_str_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_str_1275_ = lean_ctor_get(v_x_1261_, 1);
v_str_1276_ = lean_ctor_get(v_pre_1262_, 1);
v_str_1277_ = lean_ctor_get(v_pre_1263_, 1);
v___x_1278_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1279_ = lean_string_dec_eq(v_str_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1281_ = lean_string_dec_eq(v_str_1276_, v___x_1280_);
if (v___x_1281_ == 0)
{
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1283_ = lean_string_dec_eq(v_str_1275_, v___x_1282_);
if (v___x_1283_ == 0)
{
return v___x_1283_;
}
else
{
return v_suppressElabErrors_1259_;
}
}
}
}
else
{
return v___y_1260_;
}
}
default: 
{
return v___y_1260_;
}
}
}
case 0:
{
lean_object* v_str_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_str_1284_ = lean_ctor_get(v_x_1261_, 1);
v___x_1285_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1286_ = lean_string_dec_eq(v_str_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
return v___x_1286_;
}
else
{
return v_suppressElabErrors_1259_;
}
}
default: 
{
return v___y_1260_;
}
}
}
else
{
return v___y_1260_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_1259_ = stack[0].m_num;
uint8_t v___y_1260_ = stack[1].m_num;
lean_object* v_x_1261_ = stack[2].m_obj;
uint8_t v_res_1287_;
v_res_1287_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_1259_, v___y_1260_, v_x_1261_);
stack->m_num = v_res_1287_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1288_, lean_object* v___y_1289_, lean_object* v_x_1290_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1291_; uint8_t v___y_7545__boxed_1292_; uint8_t v_res_1293_; lean_object* v_r_1294_; 
v_suppressElabErrors_boxed_1291_ = lean_unbox(v_suppressElabErrors_1288_);
v___y_7545__boxed_1292_ = lean_unbox(v___y_1289_);
v_res_1293_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1291_, v___y_7545__boxed_1292_, v_x_1290_);
lean_dec(v_x_1290_);
v_r_1294_ = lean_box(v_res_1293_);
return v_r_1294_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; lean_object* v_env_1302_; uint8_t v___x_1303_; lean_object* v_env_1304_; lean_object* v___x_1305_; lean_object* v_toCold_1306_; lean_object* v_mctx_1307_; lean_object* v_lctx_1308_; lean_object* v_options_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1301_ = lean_st_ref_get(v___y_1299_);
v_env_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc_ref(v_env_1302_);
lean_dec(v___x_1301_);
v___x_1303_ = 0;
v_env_1304_ = l_Lean_Environment_setRecordingDeps(v_env_1302_, v___x_1303_);
v___x_1305_ = lean_st_ref_get(v___y_1297_);
v_toCold_1306_ = lean_ctor_get(v___y_1298_, 0);
v_mctx_1307_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_mctx_1307_);
lean_dec(v___x_1305_);
v_lctx_1308_ = lean_ctor_get(v___y_1296_, 2);
v_options_1309_ = lean_ctor_get(v_toCold_1306_, 2);
lean_inc_ref(v_options_1309_);
lean_inc_ref(v_lctx_1308_);
v___x_1310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1310_, 0, v_env_1304_);
lean_ctor_set(v___x_1310_, 1, v_mctx_1307_);
lean_ctor_set(v___x_1310_, 2, v_lctx_1308_);
lean_ctor_set(v___x_1310_, 3, v_options_1309_);
v___x_1311_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_msgData_1295_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1295_ = stack[0].m_obj;
lean_object* v___y_1296_ = stack[1].m_obj;
lean_object* v___y_1297_ = stack[2].m_obj;
lean_object* v___y_1298_ = stack[3].m_obj;
lean_object* v___y_1299_ = stack[4].m_obj;
lean_object* v_res_1313_;
v_res_1313_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msgData_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msgData_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1320_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object* v_ref_1321_, lean_object* v_msgData_1322_, uint8_t v_severity_1323_, uint8_t v_isSilent_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v_toCold_1338_; lean_object* v___y_1339_; lean_object* v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; uint8_t v___y_1405_; uint8_t v___y_1406_; uint8_t v___y_1407_; uint8_t v___x_1418_; uint8_t v___y_1420_; uint8_t v___y_1421_; uint8_t v___y_1422_; uint8_t v___y_1424_; uint8_t v___x_1432_; 
v___x_1418_ = 2;
v___x_1432_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1323_, v___x_1418_);
if (v___x_1432_ == 0)
{
v___y_1424_ = v___x_1432_;
goto v___jp_1423_;
}
else
{
uint8_t v___x_1433_; 
lean_inc_ref(v_msgData_1322_);
v___x_1433_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1322_);
v___y_1424_ = v___x_1433_;
goto v___jp_1423_;
}
v___jp_1330_:
{
lean_object* v_currNamespace_1340_; lean_object* v_openDecls_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_env_1346_; lean_object* v_nextMacroScope_1347_; lean_object* v_ngen_1348_; lean_object* v_auxDeclNGen_1349_; lean_object* v_traceState_1350_; lean_object* v_cache_1351_; lean_object* v_recordedDeps_1352_; lean_object* v_messages_1353_; lean_object* v_infoState_1354_; lean_object* v_snapshotTasks_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1366_; 
v_currNamespace_1340_ = lean_ctor_get(v_toCold_1338_, 4);
v_openDecls_1341_ = lean_ctor_get(v_toCold_1338_, 5);
lean_inc(v_openDecls_1341_);
lean_inc(v_currNamespace_1340_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v_currNamespace_1340_);
lean_ctor_set(v___x_1342_, 1, v_openDecls_1341_);
v___x_1343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v___y_1336_);
lean_inc_ref(v___y_1333_);
lean_inc_ref(v___y_1335_);
v___x_1344_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1344_, 0, v___y_1335_);
lean_ctor_set(v___x_1344_, 1, v___y_1337_);
lean_ctor_set(v___x_1344_, 2, v___y_1331_);
lean_ctor_set(v___x_1344_, 3, v___y_1333_);
lean_ctor_set(v___x_1344_, 4, v___x_1343_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*5, v___y_1334_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*5 + 1, v___y_1332_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*5 + 2, v_isSilent_1324_);
v___x_1345_ = lean_st_ref_take(v___y_1339_);
v_env_1346_ = lean_ctor_get(v___x_1345_, 0);
v_nextMacroScope_1347_ = lean_ctor_get(v___x_1345_, 1);
v_ngen_1348_ = lean_ctor_get(v___x_1345_, 2);
v_auxDeclNGen_1349_ = lean_ctor_get(v___x_1345_, 3);
v_traceState_1350_ = lean_ctor_get(v___x_1345_, 4);
v_cache_1351_ = lean_ctor_get(v___x_1345_, 5);
v_recordedDeps_1352_ = lean_ctor_get(v___x_1345_, 6);
v_messages_1353_ = lean_ctor_get(v___x_1345_, 7);
v_infoState_1354_ = lean_ctor_get(v___x_1345_, 8);
v_snapshotTasks_1355_ = lean_ctor_get(v___x_1345_, 9);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1357_ = v___x_1345_;
v_isShared_1358_ = v_isSharedCheck_1366_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snapshotTasks_1355_);
lean_inc(v_infoState_1354_);
lean_inc(v_messages_1353_);
lean_inc(v_recordedDeps_1352_);
lean_inc(v_cache_1351_);
lean_inc(v_traceState_1350_);
lean_inc(v_auxDeclNGen_1349_);
lean_inc(v_ngen_1348_);
lean_inc(v_nextMacroScope_1347_);
lean_inc(v_env_1346_);
lean_dec(v___x_1345_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1366_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = l_Lean_MessageLog_add(v___x_1344_, v_messages_1353_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 7, v___x_1360_);
v___x_1362_ = v___x_1357_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_env_1346_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_nextMacroScope_1347_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_ngen_1348_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_auxDeclNGen_1349_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_traceState_1350_);
lean_ctor_set(v_reuseFailAlloc_1365_, 5, v_cache_1351_);
lean_ctor_set(v_reuseFailAlloc_1365_, 6, v_recordedDeps_1352_);
lean_ctor_set(v_reuseFailAlloc_1365_, 7, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1365_, 8, v_infoState_1354_);
lean_ctor_set(v_reuseFailAlloc_1365_, 9, v_snapshotTasks_1355_);
v___x_1362_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_st_ref_put(v___y_1339_, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1359_);
return v___x_1364_;
}
}
}
v___jp_1367_:
{
lean_object* v_fileName_1376_; lean_object* v_fileMap_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1393_; 
v_fileName_1376_ = lean_ctor_get(v___y_1374_, 0);
v_fileMap_1377_ = lean_ctor_get(v___y_1374_, 1);
v___x_1378_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1322_);
v___x_1379_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v___x_1378_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1393_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1393_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_inc_ref_n(v_fileMap_1377_, 2);
v___x_1384_ = l_Lean_FileMap_toPosition(v_fileMap_1377_, v___y_1371_);
lean_dec(v___y_1371_);
v___x_1385_ = l_Lean_FileMap_toPosition(v_fileMap_1377_, v___y_1375_);
lean_dec(v___y_1375_);
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
v___x_1387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
if (v___y_1370_ == 0)
{
lean_del_object(v___x_1382_);
lean_dec_ref(v___y_1368_);
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1372_;
v___y_1333_ = v___x_1387_;
v___y_1334_ = v___y_1373_;
v___y_1335_ = v_fileName_1376_;
v___y_1336_ = v_a_1380_;
v___y_1337_ = v___x_1384_;
v_toCold_1338_ = v___y_1369_;
v___y_1339_ = v___y_1328_;
goto v___jp_1330_;
}
else
{
uint8_t v___x_1388_; 
lean_inc(v_a_1380_);
v___x_1388_ = l_Lean_MessageData_hasTag(v___y_1368_, v_a_1380_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_dec_ref_known(v___x_1386_, 1);
lean_dec_ref(v___x_1384_);
lean_dec(v_a_1380_);
v___x_1389_ = lean_box(0);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1389_);
v___x_1391_ = v___x_1382_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
lean_del_object(v___x_1382_);
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1372_;
v___y_1333_ = v___x_1387_;
v___y_1334_ = v___y_1373_;
v___y_1335_ = v_fileName_1376_;
v___y_1336_ = v_a_1380_;
v___y_1337_ = v___x_1384_;
v_toCold_1338_ = v___y_1369_;
v___y_1339_ = v___y_1328_;
goto v___jp_1330_;
}
}
}
}
v___jp_1394_:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Syntax_getTailPos_x3f(v___y_1400_, v___y_1399_);
lean_dec(v___y_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_inc(v___y_1401_);
v___y_1368_ = v___y_1396_;
v___y_1369_ = v___y_1397_;
v___y_1370_ = v___y_1395_;
v___y_1371_ = v___y_1401_;
v___y_1372_ = v___y_1398_;
v___y_1373_ = v___y_1399_;
v___y_1374_ = v___y_1397_;
v___y_1375_ = v___y_1401_;
goto v___jp_1367_;
}
else
{
lean_object* v_val_1403_; 
v_val_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___y_1368_ = v___y_1396_;
v___y_1369_ = v___y_1397_;
v___y_1370_ = v___y_1395_;
v___y_1371_ = v___y_1401_;
v___y_1372_ = v___y_1398_;
v___y_1373_ = v___y_1399_;
v___y_1374_ = v___y_1397_;
v___y_1375_ = v_val_1403_;
goto v___jp_1367_;
}
}
v___jp_1404_:
{
lean_object* v_toCold_1408_; lean_object* v_ref_1409_; uint8_t v_suppressElabErrors_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v_ref_1414_; lean_object* v___x_1415_; 
v_toCold_1408_ = lean_ctor_get(v___y_1327_, 0);
v_ref_1409_ = lean_ctor_get(v___y_1327_, 2);
v_suppressElabErrors_1410_ = lean_ctor_get_uint8(v___y_1327_, sizeof(void*)*3 + 2);
v___x_1411_ = lean_box(v_suppressElabErrors_1410_);
v___x_1412_ = lean_box(v___y_1405_);
v___f_1413_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1413_, 0, v___x_1411_);
lean_closure_set(v___f_1413_, 1, v___x_1412_);
v_ref_1414_ = l_Lean_replaceRef(v_ref_1321_, v_ref_1409_);
v___x_1415_ = l_Lean_Syntax_getPos_x3f(v_ref_1414_, v___y_1406_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_unsigned_to_nat(0u);
v___y_1395_ = v_suppressElabErrors_1410_;
v___y_1396_ = v___f_1413_;
v___y_1397_ = v_toCold_1408_;
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___y_1406_;
v___y_1400_ = v_ref_1414_;
v___y_1401_ = v___x_1416_;
goto v___jp_1394_;
}
else
{
lean_object* v_val_1417_; 
v_val_1417_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1417_);
lean_dec_ref_known(v___x_1415_, 1);
v___y_1395_ = v_suppressElabErrors_1410_;
v___y_1396_ = v___f_1413_;
v___y_1397_ = v_toCold_1408_;
v___y_1398_ = v___y_1407_;
v___y_1399_ = v___y_1406_;
v___y_1400_ = v_ref_1414_;
v___y_1401_ = v_val_1417_;
goto v___jp_1394_;
}
}
v___jp_1419_:
{
if (v___y_1422_ == 0)
{
v___y_1405_ = v___y_1420_;
v___y_1406_ = v___y_1421_;
v___y_1407_ = v_severity_1323_;
goto v___jp_1404_;
}
else
{
v___y_1405_ = v___y_1420_;
v___y_1406_ = v___y_1421_;
v___y_1407_ = v___x_1418_;
goto v___jp_1404_;
}
}
v___jp_1423_:
{
if (v___y_1424_ == 0)
{
uint8_t v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = 1;
v___x_1426_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1323_, v___x_1425_);
if (v___x_1426_ == 0)
{
v___y_1420_ = v___y_1424_;
v___y_1421_ = v___y_1424_;
v___y_1422_ = v___x_1426_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1327_);
v___x_1428_ = l_Lean_warningAsError;
v___x_1429_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v___x_1427_, v___x_1428_);
lean_dec_ref(v___x_1427_);
v___y_1420_ = v___y_1424_;
v___y_1421_ = v___y_1424_;
v___y_1422_ = v___x_1429_;
goto v___jp_1419_;
}
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_msgData_1322_);
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1321_ = stack[0].m_obj;
lean_object* v_msgData_1322_ = stack[1].m_obj;
uint8_t v_severity_1323_ = stack[2].m_num;
uint8_t v_isSilent_1324_ = stack[3].m_num;
lean_object* v___y_1325_ = stack[4].m_obj;
lean_object* v___y_1326_ = stack[5].m_obj;
lean_object* v___y_1327_ = stack[6].m_obj;
lean_object* v___y_1328_ = stack[7].m_obj;
lean_object* v_res_1434_;
v_res_1434_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1321_, v_msgData_1322_, v_severity_1323_, v_isSilent_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
stack->m_obj
 = v_res_1434_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1435_, lean_object* v_msgData_1436_, lean_object* v_severity_1437_, lean_object* v_isSilent_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
uint8_t v_severity_boxed_1444_; uint8_t v_isSilent_boxed_1445_; lean_object* v_res_1446_; 
v_severity_boxed_1444_ = lean_unbox(v_severity_1437_);
v_isSilent_boxed_1445_ = lean_unbox(v_isSilent_1438_);
v_res_1446_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1435_, v_msgData_1436_, v_severity_boxed_1444_, v_isSilent_boxed_1445_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_ref_1435_);
return v_res_1446_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object* v_msgData_1447_, uint8_t v_severity_1448_, uint8_t v_isSilent_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_ref_1455_; lean_object* v___x_1456_; 
v_ref_1455_ = lean_ctor_get(v___y_1452_, 2);
v___x_1456_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1455_, v_msgData_1447_, v_severity_1448_, v_isSilent_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1456_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1447_ = stack[0].m_obj;
uint8_t v_severity_1448_ = stack[1].m_num;
uint8_t v_isSilent_1449_ = stack[2].m_num;
lean_object* v___y_1450_ = stack[3].m_obj;
lean_object* v___y_1451_ = stack[4].m_obj;
lean_object* v___y_1452_ = stack[5].m_obj;
lean_object* v___y_1453_ = stack[6].m_obj;
lean_object* v_res_1457_;
v_res_1457_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1447_, v_severity_1448_, v_isSilent_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
stack->m_obj
 = v_res_1457_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object* v_msgData_1458_, lean_object* v_severity_1459_, lean_object* v_isSilent_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_severity_boxed_1466_; uint8_t v_isSilent_boxed_1467_; lean_object* v_res_1468_; 
v_severity_boxed_1466_ = lean_unbox(v_severity_1459_);
v_isSilent_boxed_1467_ = lean_unbox(v_isSilent_1460_);
v_res_1468_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1458_, v_severity_boxed_1466_, v_isSilent_boxed_1467_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1468_;
}
}
lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object* v_msgData_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = 1;
v___x_1476_ = 0;
v___x_1477_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1469_, v___x_1475_, v___x_1476_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1477_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1469_ = stack[0].m_obj;
lean_object* v___y_1470_ = stack[1].m_obj;
lean_object* v___y_1471_ = stack[2].m_obj;
lean_object* v___y_1472_ = stack[3].m_obj;
lean_object* v___y_1473_ = stack[4].m_obj;
lean_object* v_res_1478_;
v_res_1478_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v_msgData_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
stack->m_obj
 = v_res_1478_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object* v_msgData_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v_msgData_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
return v_res_1485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2));
v___x_1491_ = l_Lean_stringToMessageData(v___x_1490_);
return v___x_1491_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object* v___x_1492_, lean_object* v___x_1493_, lean_object* v___x_1494_, lean_object* v___x_1495_, lean_object* v_cfgStx_1496_, lean_object* v_tk_1497_, lean_object* v_typesStx_1498_, lean_object* v___x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_ref_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___y_1516_; 
v_ref_1505_ = lean_ctor_get(v___y_1502_, 2);
v___x_1506_ = 0;
v___x_1507_ = l_Lean_SourceInfo_fromRef(v_ref_1505_, v___x_1506_);
v___x_1508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1));
v___x_1509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6));
v___x_1510_ = l_Lean_Name_mkStr5(v___x_1492_, v___x_1493_, v___x_1494_, v___x_1495_, v___x_1509_);
v___x_1511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1507_);
v___x_1512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1507_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1498_) == 1)
{
lean_object* v_val_1537_; lean_object* v___x_1538_; 
v_val_1537_ = lean_ctor_get(v_typesStx_1498_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v_typesStx_1498_, 1);
v___x_1538_ = l_Array_mkArray1___redArg(v_val_1537_);
v___y_1516_ = v___x_1538_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1539_; 
lean_dec(v_typesStx_1498_);
v___x_1539_ = lean_mk_empty_array_with_capacity(v___x_1499_);
v___y_1516_ = v___x_1539_;
goto v___jp_1515_;
}
v___jp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = l_Array_append___redArg(v___x_1514_, v___y_1516_);
lean_dec_ref(v___y_1516_);
lean_inc(v___x_1507_);
v___x_1518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1507_);
lean_ctor_set(v___x_1518_, 1, v___x_1513_);
lean_ctor_set(v___x_1518_, 2, v___x_1517_);
v___x_1519_ = l_Lean_Syntax_node3(v___x_1507_, v___x_1510_, v___x_1512_, v_cfgStx_1496_, v___x_1518_);
v___x_1520_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3);
v___x_1521_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v___x_1520_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1535_; 
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1521_, 0);
lean_dec(v_unused_1536_);
v___x_1523_ = v___x_1521_;
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
else
{
lean_dec(v___x_1521_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1508_);
lean_ctor_set(v___x_1525_, 1, v___x_1519_);
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
lean_ctor_set(v___x_1527_, 2, v___x_1526_);
lean_ctor_set(v___x_1527_, 3, v___x_1526_);
lean_ctor_set(v___x_1527_, 4, v___x_1526_);
lean_ctor_set(v___x_1527_, 5, v___x_1526_);
lean_inc(v_ref_1505_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set_tag(v___x_1523_, 1);
lean_ctor_set(v___x_1523_, 0, v_ref_1505_);
v___x_1529_ = v___x_1523_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_ref_1505_);
v___x_1529_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1531_ = 4;
v___x_1532_ = l_Lean_MessageData_nil;
v___x_1533_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1497_, v___x_1527_, v___x_1529_, v___x_1530_, v___x_1526_, v___x_1531_, v___x_1532_, v___y_1502_, v___y_1503_);
return v___x_1533_;
}
}
}
else
{
lean_dec(v___x_1519_);
lean_dec(v_tk_1497_);
return v___x_1521_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1492_ = stack[0].m_obj;
lean_object* v___x_1493_ = stack[1].m_obj;
lean_object* v___x_1494_ = stack[2].m_obj;
lean_object* v___x_1495_ = stack[3].m_obj;
lean_object* v_cfgStx_1496_ = stack[4].m_obj;
lean_object* v_tk_1497_ = stack[5].m_obj;
lean_object* v_typesStx_1498_ = stack[6].m_obj;
lean_object* v___x_1499_ = stack[7].m_obj;
lean_object* v___y_1500_ = stack[8].m_obj;
lean_object* v___y_1501_ = stack[9].m_obj;
lean_object* v___y_1502_ = stack[10].m_obj;
lean_object* v___y_1503_ = stack[11].m_obj;
lean_object* v_res_1540_;
v_res_1540_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(v___x_1492_, v___x_1493_, v___x_1494_, v___x_1495_, v_cfgStx_1496_, v_tk_1497_, v_typesStx_1498_, v___x_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
stack->m_obj
 = v_res_1540_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object* v___x_1541_, lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v_cfgStx_1545_, lean_object* v_tk_1546_, lean_object* v_typesStx_1547_, lean_object* v___x_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(v___x_1541_, v___x_1542_, v___x_1543_, v___x_1544_, v_cfgStx_1545_, v_tk_1546_, v_typesStx_1547_, v___x_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___x_1548_);
return v_res_1554_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(lean_object* v_x_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_1571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_1572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_1574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
lean_inc(v_x_1560_);
v___x_1575_ = l_Lean_Syntax_isOfKind(v_x_1560_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec(v_x_1560_);
v___x_1576_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1576_;
}
else
{
lean_object* v___x_1577_; lean_object* v_cfgStx_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1577_ = lean_unsigned_to_nat(1u);
v_cfgStx_1578_ = l_Lean_Syntax_getArg(v_x_1560_, v___x_1577_);
v___x_1579_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_1578_);
v___x_1580_ = l_Lean_Syntax_isOfKind(v_cfgStx_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec(v_cfgStx_1578_);
lean_dec(v_x_1560_);
v___x_1581_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; lean_object* v_tk_1583_; lean_object* v_typesStx_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1582_ = lean_unsigned_to_nat(0u);
v_tk_1583_ = l_Lean_Syntax_getArg(v_x_1560_, v___x_1582_);
v___x_1656_ = lean_unsigned_to_nat(2u);
v___x_1657_ = l_Lean_Syntax_getArg(v_x_1560_, v___x_1656_);
v___x_1658_ = l_Lean_Syntax_isNone(v___x_1657_);
if (v___x_1658_ == 0)
{
uint8_t v___x_1659_; 
lean_inc(v___x_1657_);
v___x_1659_ = l_Lean_Syntax_matchesNull(v___x_1657_, v___x_1577_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec(v___x_1657_);
lean_dec(v_tk_1583_);
lean_dec(v_cfgStx_1578_);
lean_dec(v_x_1560_);
v___x_1660_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1660_;
}
else
{
lean_object* v_typesStx_1661_; 
v_typesStx_1661_ = l_Lean_Syntax_getArg(v___x_1657_, v___x_1582_);
lean_dec(v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1661_);
v___x_1665_ = l_Lean_Syntax_isOfKind(v_typesStx_1661_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec(v_typesStx_1661_);
lean_dec(v_tk_1583_);
lean_dec(v_cfgStx_1578_);
lean_dec(v_x_1560_);
v___x_1666_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1666_;
}
else
{
goto v___jp_1662_;
}
}
else
{
goto v___jp_1662_;
}
v___jp_1662_:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_typesStx_1661_);
v_typesStx_1585_ = v___x_1663_;
v___y_1586_ = v_a_1561_;
v___y_1587_ = v_a_1562_;
v___y_1588_ = v_a_1563_;
v___y_1589_ = v_a_1564_;
v___y_1590_ = v_a_1565_;
v___y_1591_ = v_a_1566_;
v___y_1592_ = v_a_1567_;
v___y_1593_ = v_a_1568_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v___x_1667_; 
lean_dec(v___x_1657_);
v___x_1667_ = lean_box(0);
v_typesStx_1585_ = v___x_1667_;
v___y_1586_ = v_a_1561_;
v___y_1587_ = v_a_1562_;
v___y_1588_ = v_a_1563_;
v___y_1589_ = v_a_1564_;
v___y_1590_ = v_a_1565_;
v___y_1591_ = v_a_1566_;
v___y_1592_ = v_a_1567_;
v___y_1593_ = v_a_1568_;
goto v___jp_1584_;
}
v___jp_1584_:
{
lean_object* v___x_1594_; lean_object* v_path_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1594_ = lean_unsigned_to_nat(3u);
v_path_1595_ = l_Lean_Syntax_getArg(v_x_1560_, v___x_1594_);
lean_dec(v_x_1560_);
v___x_1596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1));
lean_inc(v_path_1595_);
v___x_1597_ = l_Lean_Syntax_isOfKind(v_path_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
lean_dec(v_path_1595_);
lean_dec(v_typesStx_1585_);
lean_dec(v_tk_1583_);
lean_dec(v_cfgStx_1578_);
v___x_1598_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1598_;
}
else
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
lean_inc(v_typesStx_1585_);
lean_inc(v_cfgStx_1578_);
v___f_1599_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1599_, 0, v___x_1570_);
lean_closure_set(v___f_1599_, 1, v___x_1571_);
lean_closure_set(v___f_1599_, 2, v___x_1572_);
lean_closure_set(v___f_1599_, 3, v___x_1573_);
lean_closure_set(v___f_1599_, 4, v_cfgStx_1578_);
lean_closure_set(v___f_1599_, 5, v_tk_1583_);
lean_closure_set(v___f_1599_, 6, v_typesStx_1585_);
lean_closure_set(v___f_1599_, 7, v___x_1582_);
v___x_1600_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1654_; 
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v___x_1600_, 0);
lean_dec(v_unused_1655_);
v___x_1602_ = v___x_1600_;
v_isShared_1603_ = v_isSharedCheck_1654_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v___x_1600_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1654_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1587_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v_mvarId_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v_mvarId_1606_ = lean_ctor_get(v_a_1605_, 1);
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2));
lean_inc(v_mvarId_1606_);
v___x_1608_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_1578_, v_mvarId_1606_, v___x_1607_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1610_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1585_, v_a_1609_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = l_Lean_TSyntax_getString(v_path_1595_);
lean_dec(v_path_1595_);
v___x_1613_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_1612_, v_a_1609_, v_a_1611_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 1);
lean_ctor_set(v___x_1602_, 0, v_a_1605_);
v___x_1616_ = v___x_1602_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1605_);
v___x_1616_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_1617_, 0, v___x_1616_);
lean_closure_set(v___x_1617_, 1, v_a_1614_);
lean_closure_set(v___x_1617_, 2, v___f_1599_);
v___x_1618_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1617_, v___y_1586_, v___y_1587_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec_ref_known(v___x_1618_, 1);
v___x_1619_ = lean_box(0);
v___x_1620_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1619_, v___y_1587_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1620_;
}
else
{
return v___x_1618_;
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1605_);
lean_del_object(v___x_1602_);
lean_dec_ref(v___f_1599_);
v_a_1622_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1613_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1613_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_a_1609_);
lean_dec(v_a_1605_);
lean_del_object(v___x_1602_);
lean_dec_ref(v___f_1599_);
lean_dec(v_path_1595_);
v_a_1630_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1610_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1610_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_a_1605_);
lean_del_object(v___x_1602_);
lean_dec_ref(v___f_1599_);
lean_dec(v_path_1595_);
lean_dec(v_typesStx_1585_);
v_a_1638_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1608_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1608_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_del_object(v___x_1602_);
lean_dec_ref(v___f_1599_);
lean_dec(v_path_1595_);
lean_dec(v_typesStx_1585_);
lean_dec(v_cfgStx_1578_);
v_a_1646_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1604_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1604_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_1599_);
lean_dec(v_path_1595_);
lean_dec(v_typesStx_1585_);
lean_dec(v_cfgStx_1578_);
return v___x_1600_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1560_ = stack[0].m_obj;
lean_object* v_a_1561_ = stack[1].m_obj;
lean_object* v_a_1562_ = stack[2].m_obj;
lean_object* v_a_1563_ = stack[3].m_obj;
lean_object* v_a_1564_ = stack[4].m_obj;
lean_object* v_a_1565_ = stack[5].m_obj;
lean_object* v_a_1566_ = stack[6].m_obj;
lean_object* v_a_1567_ = stack[7].m_obj;
lean_object* v_a_1568_ = stack[8].m_obj;
lean_object* v_res_1668_;
v_res_1668_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(v_x_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
stack->m_obj
 = v_res_1668_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed(lean_object* v_x_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(v_x_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
return v_res_1679_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1(){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1685_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1));
v___x_1688_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed), 10, 0);
v___x_1689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1685_, v___x_1686_, v___x_1687_, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1690_;
v_res_1690_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
stack->m_obj
 = v_res_1690_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___boxed(lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
return v_res_1692_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1693_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1);
v___x_1697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
lean_ctor_set(v___x_1697_, 2, v___x_1696_);
lean_ctor_set(v___x_1697_, 3, v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_unsigned_to_nat(16u);
v___x_1700_ = lean_mk_array(v___x_1699_, v___x_1698_);
return v___x_1700_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3);
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4);
v___x_1705_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
lean_ctor_set(v___x_1705_, 2, v___x_1704_);
lean_ctor_set(v___x_1705_, 3, v___x_1704_);
return v___x_1705_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object* v___x_1708_, lean_object* v___x_1709_, lean_object* v___x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1721_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_1722_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_1723_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_1724_ = 0;
v___x_1725_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1725_, 0, v___x_1721_);
lean_ctor_set(v___x_1725_, 1, v___x_1722_);
lean_ctor_set(v___x_1725_, 2, v___x_1708_);
lean_ctor_set(v___x_1725_, 3, v___x_1723_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*4, v___x_1724_);
v___x_1726_ = lean_st_mk_ref(v___x_1725_);
v___x_1727_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1709_, v___x_1710_, v___x_1726_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1732_ = lean_st_ref_get(v___x_1726_);
lean_dec(v___x_1726_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1728_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v___x_1726_);
v_a_1738_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1727_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1727_);
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
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1708_ = stack[0].m_obj;
lean_object* v___x_1709_ = stack[1].m_obj;
lean_object* v___x_1710_ = stack[2].m_obj;
lean_object* v___y_1711_ = stack[3].m_obj;
lean_object* v___y_1712_ = stack[4].m_obj;
lean_object* v___y_1713_ = stack[5].m_obj;
lean_object* v___y_1714_ = stack[6].m_obj;
lean_object* v___y_1715_ = stack[7].m_obj;
lean_object* v___y_1716_ = stack[8].m_obj;
lean_object* v___y_1717_ = stack[9].m_obj;
lean_object* v___y_1718_ = stack[10].m_obj;
lean_object* v___y_1719_ = stack[11].m_obj;
lean_object* v_res_1746_;
v_res_1746_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(v___x_1708_, v___x_1709_, v___x_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
stack->m_obj
 = v_res_1746_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object* v___x_1747_, lean_object* v___x_1748_, lean_object* v___x_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(v___x_1747_, v___x_1748_, v___x_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___x_1749_);
lean_dec(v___x_1748_);
return v_res_1760_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1761_, lean_object* v_i_1762_, lean_object* v_k_1763_){
_start:
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_array_get_size(v_keys_1761_);
v___x_1765_ = lean_nat_dec_lt(v_i_1762_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_dec(v_i_1762_);
return v___x_1765_;
}
else
{
lean_object* v_k_x27_1766_; uint8_t v___x_1767_; 
v_k_x27_1766_ = lean_array_fget_borrowed(v_keys_1761_, v_i_1762_);
v___x_1767_ = l_Lean_instBEqMVarId_beq(v_k_1763_, v_k_x27_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_add(v_i_1762_, v___x_1768_);
lean_dec(v_i_1762_);
v_i_1762_ = v___x_1769_;
goto _start;
}
else
{
lean_dec(v_i_1762_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1761_ = stack[0].m_obj;
lean_object* v_i_1762_ = stack[1].m_obj;
lean_object* v_k_1763_ = stack[2].m_obj;
uint8_t v_res_1771_;
v_res_1771_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1761_, v_i_1762_, v_k_1763_);
stack->m_num = v_res_1771_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1772_, lean_object* v_i_1773_, lean_object* v_k_1774_){
_start:
{
uint8_t v_res_1775_; lean_object* v_r_1776_; 
v_res_1775_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1772_, v_i_1773_, v_k_1774_);
lean_dec(v_k_1774_);
lean_dec_ref(v_keys_1772_);
v_r_1776_ = lean_box(v_res_1775_);
return v_r_1776_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1777_, size_t v_x_1778_, lean_object* v_x_1779_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 0)
{
lean_object* v_es_1780_; lean_object* v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; lean_object* v_j_1784_; lean_object* v___x_1785_; 
v_es_1780_ = lean_ctor_get(v_x_1777_, 0);
v___x_1781_ = lean_box(2);
v___x_1782_ = ((size_t)31ULL);
v___x_1783_ = lean_usize_land(v_x_1778_, v___x_1782_);
v_j_1784_ = lean_usize_to_nat(v___x_1783_);
v___x_1785_ = lean_array_get_borrowed(v___x_1781_, v_es_1780_, v_j_1784_);
lean_dec(v_j_1784_);
switch(lean_obj_tag(v___x_1785_))
{
case 0:
{
lean_object* v_key_1786_; uint8_t v___x_1787_; 
v_key_1786_ = lean_ctor_get(v___x_1785_, 0);
v___x_1787_ = l_Lean_instBEqMVarId_beq(v_x_1779_, v_key_1786_);
return v___x_1787_;
}
case 1:
{
lean_object* v_node_1788_; size_t v___x_1789_; size_t v___x_1790_; 
v_node_1788_ = lean_ctor_get(v___x_1785_, 0);
v___x_1789_ = ((size_t)5ULL);
v___x_1790_ = lean_usize_shift_right(v_x_1778_, v___x_1789_);
v_x_1777_ = v_node_1788_;
v_x_1778_ = v___x_1790_;
goto _start;
}
default: 
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
}
}
else
{
lean_object* v_ks_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_ks_1793_ = lean_ctor_get(v_x_1777_, 0);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1793_, v___x_1794_, v_x_1779_);
return v___x_1795_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1777_ = stack[0].m_obj;
size_t v_x_1778_ = stack[1].m_num;
lean_object* v_x_1779_ = stack[2].m_obj;
uint8_t v_res_1796_;
v_res_1796_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1777_, v_x_1778_, v_x_1779_);
stack->m_num = v_res_1796_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
size_t v_x_3575__boxed_1800_; uint8_t v_res_1801_; lean_object* v_r_1802_; 
v_x_3575__boxed_1800_ = lean_unbox_usize(v_x_1798_);
lean_dec(v_x_1798_);
v_res_1801_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1797_, v_x_3575__boxed_1800_, v_x_1799_);
lean_dec(v_x_1799_);
lean_dec_ref(v_x_1797_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
uint64_t v___x_1805_; size_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1805_ = l_Lean_instHashableMVarId_hash(v_x_1804_);
v___x_1806_ = lean_uint64_to_usize(v___x_1805_);
v___x_1807_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1803_, v___x_1806_, v_x_1804_);
return v___x_1807_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1803_ = stack[0].m_obj;
lean_object* v_x_1804_ = stack[1].m_obj;
uint8_t v_res_1808_;
v_res_1808_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1803_, v_x_1804_);
stack->m_num = v_res_1808_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1809_, lean_object* v_x_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1809_, v_x_1810_);
lean_dec(v_x_1810_);
lean_dec_ref(v_x_1809_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v_mctx_1817_; lean_object* v_eAssignment_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1816_ = lean_st_ref_get(v___y_1814_);
v_mctx_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc_ref(v_mctx_1817_);
lean_dec(v___x_1816_);
v_eAssignment_1818_ = lean_ctor_get(v_mctx_1817_, 8);
lean_inc_ref(v_eAssignment_1818_);
lean_dec_ref(v_mctx_1817_);
v___x_1819_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_1818_, v_mvarId_1813_);
lean_dec_ref(v_eAssignment_1818_);
v___x_1820_ = lean_box(v___x_1819_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1813_ = stack[0].m_obj;
lean_object* v___y_1814_ = stack[1].m_obj;
lean_object* v_res_1822_;
v_res_1822_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1813_, v___y_1814_);
stack->m_obj
 = v_res_1822_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec(v_mvarId_1823_);
return v_res_1826_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(lean_object* v_msg_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_ref_1833_; lean_object* v___x_1834_; lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_ref_1833_ = lean_ctor_get(v___y_1830_, 2);
v___x_1834_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msg_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_inc(v_ref_1833_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_ref_1833_);
lean_ctor_set(v___x_1839_, 1, v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 1);
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1827_ = stack[0].m_obj;
lean_object* v___y_1828_ = stack[1].m_obj;
lean_object* v___y_1829_ = stack[2].m_obj;
lean_object* v___y_1830_ = stack[3].m_obj;
lean_object* v___y_1831_ = stack[4].m_obj;
lean_object* v_res_1844_;
v_res_1844_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
stack->m_obj
 = v_res_1844_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg___boxed(lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1851_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1));
v___x_1856_ = l_Lean_stringToMessageData(v___x_1855_);
return v___x_1856_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(lean_object* v_x_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
lean_inc(v_x_1857_);
v___x_1868_ = l_Lean_Syntax_isOfKind(v_x_1857_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_dec(v_x_1857_);
v___x_1869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; lean_object* v_cfg_1871_; lean_object* v_types_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1870_ = lean_unsigned_to_nat(1u);
v_cfg_1871_ = l_Lean_Syntax_getArg(v_x_1857_, v___x_1870_);
v___x_1947_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_1871_);
v___x_1948_ = l_Lean_Syntax_isOfKind(v_cfg_1871_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec(v_cfg_1871_);
lean_dec(v_x_1857_);
v___x_1949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_unsigned_to_nat(2u);
v___x_1951_ = l_Lean_Syntax_getArg(v_x_1857_, v___x_1950_);
lean_dec(v_x_1857_);
v___x_1952_ = l_Lean_Syntax_isNone(v___x_1951_);
if (v___x_1952_ == 0)
{
uint8_t v___x_1953_; 
lean_inc(v___x_1951_);
v___x_1953_ = l_Lean_Syntax_matchesNull(v___x_1951_, v___x_1870_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec(v___x_1951_);
lean_dec(v_cfg_1871_);
v___x_1954_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v_types_1956_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v_types_1956_ = l_Lean_Syntax_getArg(v___x_1951_, v___x_1955_);
lean_dec(v___x_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_1956_);
v___x_1960_ = l_Lean_Syntax_isOfKind(v_types_1956_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec(v_types_1956_);
lean_dec(v_cfg_1871_);
v___x_1961_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1961_;
}
else
{
goto v___jp_1957_;
}
}
else
{
goto v___jp_1957_;
}
v___jp_1957_:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_types_1956_);
v_types_1873_ = v___x_1958_;
v___y_1874_ = v_a_1858_;
v___y_1875_ = v_a_1859_;
v___y_1876_ = v_a_1860_;
v___y_1877_ = v_a_1861_;
v___y_1878_ = v_a_1862_;
v___y_1879_ = v_a_1863_;
v___y_1880_ = v_a_1864_;
v___y_1881_ = v_a_1865_;
goto v___jp_1872_;
}
}
}
else
{
lean_object* v___x_1962_; 
lean_dec(v___x_1951_);
v___x_1962_ = lean_box(0);
v_types_1873_ = v___x_1962_;
v___y_1874_ = v_a_1858_;
v___y_1875_ = v_a_1859_;
v___y_1876_ = v_a_1860_;
v___y_1877_ = v_a_1861_;
v___y_1878_ = v_a_1862_;
v___y_1879_ = v_a_1863_;
v___y_1880_ = v_a_1864_;
v___y_1881_ = v_a_1865_;
goto v___jp_1872_;
}
}
v___jp_1872_:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1945_; 
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1882_, 0);
lean_dec(v_unused_1946_);
v___x_1884_ = v___x_1882_;
v_isShared_1885_ = v_isSharedCheck_1945_;
goto v_resetjp_1883_;
}
else
{
lean_dec(v___x_1882_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1945_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1875_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_mvarId_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v_mvarId_1888_ = lean_ctor_get(v_a_1887_, 1);
v___x_1889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0));
lean_inc(v_mvarId_1888_);
v___x_1890_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_1871_, v_mvarId_1888_, v___x_1889_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1873_, v_a_1891_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v_a_1893_);
v___x_1895_ = v___x_1884_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1893_);
v___x_1895_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_1895_, v_a_1891_, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1887_);
v___f_1899_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1899_, 0, v___x_1898_);
lean_closure_set(v___f_1899_, 1, v___x_1896_);
lean_closure_set(v___f_1899_, 2, v___x_1897_);
v___x_1900_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_1899_, v___y_1874_, v___y_1875_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v_snd_1902_; lean_object* v_target_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_a_1906_; uint8_t v___x_1907_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v_snd_1902_ = lean_ctor_get(v_a_1901_, 1);
lean_inc(v_snd_1902_);
lean_dec(v_a_1901_);
v_target_1903_ = lean_ctor_get(v_snd_1902_, 2);
lean_inc_ref(v_target_1903_);
lean_dec(v_snd_1902_);
v___x_1904_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1903_);
lean_dec_ref(v_target_1903_);
v___x_1905_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v___x_1904_, v___y_1879_);
lean_dec(v___x_1904_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = lean_unbox(v_a_1906_);
lean_dec(v_a_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2);
v___x_1909_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v___x_1908_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1910_, v___y_1875_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1911_;
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1900_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1900_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1891_);
lean_dec(v_a_1887_);
lean_del_object(v___x_1884_);
v_a_1921_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1892_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1892_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
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
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_a_1887_);
lean_del_object(v___x_1884_);
lean_dec(v_types_1873_);
v_a_1929_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1890_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1890_);
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
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1884_);
lean_dec(v_types_1873_);
lean_dec(v_cfg_1871_);
v_a_1937_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1886_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1886_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
else
{
lean_dec(v_types_1873_);
lean_dec(v_cfg_1871_);
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1857_ = stack[0].m_obj;
lean_object* v_a_1858_ = stack[1].m_obj;
lean_object* v_a_1859_ = stack[2].m_obj;
lean_object* v_a_1860_ = stack[3].m_obj;
lean_object* v_a_1861_ = stack[4].m_obj;
lean_object* v_a_1862_ = stack[5].m_obj;
lean_object* v_a_1863_ = stack[6].m_obj;
lean_object* v_a_1864_ = stack[7].m_obj;
lean_object* v_a_1865_ = stack[8].m_obj;
lean_object* v_res_1963_;
v_res_1963_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(v_x_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
stack->m_obj
 = v_res_1963_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed(lean_object* v_x_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(v_x_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
return v_res_1974_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(lean_object* v_mvarId_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1975_, v___y_1981_);
return v___x_1985_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1975_ = stack[0].m_obj;
lean_object* v___y_1976_ = stack[1].m_obj;
lean_object* v___y_1977_ = stack[2].m_obj;
lean_object* v___y_1978_ = stack[3].m_obj;
lean_object* v___y_1979_ = stack[4].m_obj;
lean_object* v___y_1980_ = stack[5].m_obj;
lean_object* v___y_1981_ = stack[6].m_obj;
lean_object* v___y_1982_ = stack[7].m_obj;
lean_object* v___y_1983_ = stack[8].m_obj;
lean_object* v_res_1986_;
v_res_1986_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(v_mvarId_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
stack->m_obj
 = v_res_1986_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(v_mvarId_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v_mvarId_1987_);
return v_res_1997_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_object* v_00_u03b1_1998_, lean_object* v_msg_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1999_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
return v___x_2009_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1999_ = stack[1].m_obj;
lean_object* v___y_2000_ = stack[2].m_obj;
lean_object* v___y_2001_ = stack[3].m_obj;
lean_object* v___y_2002_ = stack[4].m_obj;
lean_object* v___y_2003_ = stack[5].m_obj;
lean_object* v___y_2004_ = stack[6].m_obj;
lean_object* v___y_2005_ = stack[7].m_obj;
lean_object* v___y_2006_ = stack[8].m_obj;
lean_object* v___y_2007_ = stack[9].m_obj;
lean_object* v_res_2010_;
v_res_2010_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_box(0), v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
stack->m_obj
 = v_res_2010_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_msg_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(v_00_u03b1_2011_, v_msg_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2022_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_2024_, v_x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2024_ = stack[1].m_obj;
lean_object* v_x_2025_ = stack[2].m_obj;
uint8_t v_res_2027_;
v_res_2027_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_box(0), v_x_2024_, v_x_2025_);
stack->m_num = v_res_2027_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
uint8_t v_res_2031_; lean_object* v_r_2032_; 
v_res_2031_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(v_00_u03b2_2028_, v_x_2029_, v_x_2030_);
lean_dec(v_x_2030_);
lean_dec_ref(v_x_2029_);
v_r_2032_ = lean_box(v_res_2031_);
return v_r_2032_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2033_, lean_object* v_x_2034_, size_t v_x_2035_, lean_object* v_x_2036_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_2034_, v_x_2035_, v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2034_ = stack[1].m_obj;
size_t v_x_2035_ = stack[2].m_num;
lean_object* v_x_2036_ = stack[3].m_obj;
uint8_t v_res_2038_;
v_res_2038_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_box(0), v_x_2034_, v_x_2035_, v_x_2036_);
stack->m_num = v_res_2038_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_){
_start:
{
size_t v_x_4173__boxed_2043_; uint8_t v_res_2044_; lean_object* v_r_2045_; 
v_x_4173__boxed_2043_ = lean_unbox_usize(v_x_2041_);
lean_dec(v_x_2041_);
v_res_2044_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_2039_, v_x_2040_, v_x_4173__boxed_2043_, v_x_2042_);
lean_dec(v_x_2042_);
lean_dec_ref(v_x_2040_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2046_, lean_object* v_keys_2047_, lean_object* v_vals_2048_, lean_object* v_heq_2049_, lean_object* v_i_2050_, lean_object* v_k_2051_){
_start:
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2047_, v_i_2050_, v_k_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2047_ = stack[1].m_obj;
lean_object* v_vals_2048_ = stack[2].m_obj;
lean_object* v_i_2050_ = stack[4].m_obj;
lean_object* v_k_2051_ = stack[5].m_obj;
uint8_t v_res_2053_;
v_res_2053_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_keys_2047_, v_vals_2048_, lean_box(0), v_i_2050_, v_k_2051_);
stack->m_num = v_res_2053_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2054_, lean_object* v_keys_2055_, lean_object* v_vals_2056_, lean_object* v_heq_2057_, lean_object* v_i_2058_, lean_object* v_k_2059_){
_start:
{
uint8_t v_res_2060_; lean_object* v_r_2061_; 
v_res_2060_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2054_, v_keys_2055_, v_vals_2056_, v_heq_2057_, v_i_2058_, v_k_2059_);
lean_dec(v_k_2059_);
lean_dec_ref(v_vals_2056_);
lean_dec_ref(v_keys_2055_);
v_r_2061_ = lean_box(v_res_2060_);
return v_r_2061_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2067_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_2069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1));
v___x_2070_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed), 10, 0);
v___x_2071_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2067_, v___x_2068_, v___x_2069_, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2072_;
v_res_2072_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
stack->m_obj
 = v_res_2072_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___boxed(lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
return v_res_2074_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_2075_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(lean_object* v_msg_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_4094__overap_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0);
v___x_4094__overap_2089_ = lean_panic_fn_borrowed(v___x_2088_, v_msg_2076_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc(v___y_2077_);
v___x_2090_ = lean_apply_11(v___x_4094__overap_2089_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, lean_box(0));
return v___x_2090_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2076_ = stack[0].m_obj;
lean_object* v___y_2077_ = stack[1].m_obj;
lean_object* v___y_2078_ = stack[2].m_obj;
lean_object* v___y_2079_ = stack[3].m_obj;
lean_object* v___y_2080_ = stack[4].m_obj;
lean_object* v___y_2081_ = stack[5].m_obj;
lean_object* v___y_2082_ = stack[6].m_obj;
lean_object* v___y_2083_ = stack[7].m_obj;
lean_object* v___y_2084_ = stack[8].m_obj;
lean_object* v___y_2085_ = stack[9].m_obj;
lean_object* v___y_2086_ = stack[10].m_obj;
lean_object* v_res_2091_;
v_res_2091_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v_msg_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
stack->m_obj
 = v_res_2091_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___boxed(lean_object* v_msg_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v_msg_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec(v___y_2093_);
return v_res_2104_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2));
v___x_2109_ = lean_unsigned_to_nat(46u);
v___x_2110_ = lean_unsigned_to_nat(113u);
v___x_2111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1));
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0));
v___x_2113_ = l_mkPanicMessageWithDecl(v___x_2112_, v___x_2111_, v___x_2110_, v___x_2109_, v___x_2108_);
return v___x_2113_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(lean_object* v_a_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2126_ = lean_st_ref_get(v___y_2115_);
v___x_2127_ = lean_box(1);
v___x_2128_ = lean_box(0);
v___x_2129_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2127_, v_a_2114_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2126_);
v___x_2131_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_2132_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_2134_ = 0;
v___x_2135_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2131_);
lean_ctor_set(v___x_2135_, 1, v___x_2132_);
lean_ctor_set(v___x_2135_, 2, v___x_2130_);
lean_ctor_set(v___x_2135_, 3, v___x_2133_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*4, v___x_2134_);
v___x_2136_ = lean_st_mk_ref(v___x_2135_);
v___x_2137_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2128_, v___x_2129_, v___x_2136_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec_ref(v___x_2129_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2151_; 
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2137_, 0);
lean_dec(v_unused_2152_);
v___x_2139_ = v___x_2137_;
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v___x_2137_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v_target_2142_; 
v___x_2141_ = lean_st_ref_get(v___x_2136_);
lean_dec(v___x_2136_);
v_target_2142_ = lean_ctor_get(v___x_2141_, 2);
lean_inc_ref(v_target_2142_);
lean_dec(v___x_2141_);
if (lean_obj_tag(v_target_2142_) == 1)
{
lean_object* v_goal_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v_goal_2143_ = lean_ctor_get(v_target_2142_, 0);
lean_inc_ref(v_goal_2143_);
lean_dec_ref_known(v_target_2142_, 1);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_st_ref_swap(v___y_2115_, v_goal_2143_);
lean_dec(v___x_2145_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2144_);
v___x_2147_ = v___x_2139_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2144_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v_target_2142_);
lean_del_object(v___x_2139_);
v___x_2149_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3);
v___x_2150_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v___x_2149_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2150_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v___x_2136_);
v_a_2153_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2137_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2137_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
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
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2114_ = stack[0].m_obj;
lean_object* v___y_2115_ = stack[1].m_obj;
lean_object* v___y_2116_ = stack[2].m_obj;
lean_object* v___y_2117_ = stack[3].m_obj;
lean_object* v___y_2118_ = stack[4].m_obj;
lean_object* v___y_2119_ = stack[5].m_obj;
lean_object* v___y_2120_ = stack[6].m_obj;
lean_object* v___y_2121_ = stack[7].m_obj;
lean_object* v___y_2122_ = stack[8].m_obj;
lean_object* v___y_2123_ = stack[9].m_obj;
lean_object* v___y_2124_ = stack[10].m_obj;
lean_object* v_res_2161_;
v_res_2161_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(v_a_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
stack->m_obj
 = v_res_2161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed(lean_object* v_a_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(v_a_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec(v___y_2163_);
return v_res_2174_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(lean_object* v_x_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
lean_inc(v_x_2185_);
v___x_2194_ = l_Lean_Syntax_isOfKind(v_x_2185_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_dec(v_x_2185_);
v___x_2195_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; lean_object* v_cfg_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2196_ = lean_unsigned_to_nat(1u);
v_cfg_2197_ = l_Lean_Syntax_getArg(v_x_2185_, v___x_2196_);
lean_dec(v_x_2185_);
v___x_2198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_2197_);
v___x_2199_ = l_Lean_Syntax_isOfKind(v_cfg_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; 
lean_dec(v_cfg_2197_);
v___x_2200_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v___x_2202_; 
lean_dec_ref_known(v___x_2201_, 1);
v___x_2202_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_mvarId_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v_mvarId_2204_ = lean_ctor_get(v_a_2203_, 1);
lean_inc(v_mvarId_2204_);
lean_dec(v_a_2203_);
v___x_2205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3));
v___x_2206_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_2197_, v_mvarId_2204_, v___x_2205_, v_a_2190_, v_a_2191_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v___f_2208_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2208_, 0, v_a_2207_);
v___x_2209_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___f_2208_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
return v___x_2209_;
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
v_a_2210_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2206_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2206_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_cfg_2197_);
v_a_2218_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2202_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2202_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_dec(v_cfg_2197_);
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2185_ = stack[0].m_obj;
lean_object* v_a_2186_ = stack[1].m_obj;
lean_object* v_a_2187_ = stack[2].m_obj;
lean_object* v_a_2188_ = stack[3].m_obj;
lean_object* v_a_2189_ = stack[4].m_obj;
lean_object* v_a_2190_ = stack[5].m_obj;
lean_object* v_a_2191_ = stack[6].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___boxed(lean_object* v_x_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
return v_res_2235_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(lean_object* v_x_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2236_, v_a_2237_, v_a_2238_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2236_ = stack[0].m_obj;
lean_object* v_a_2237_ = stack[1].m_obj;
lean_object* v_a_2238_ = stack[2].m_obj;
lean_object* v_a_2239_ = stack[3].m_obj;
lean_object* v_a_2240_ = stack[4].m_obj;
lean_object* v_a_2241_ = stack[5].m_obj;
lean_object* v_a_2242_ = stack[6].m_obj;
lean_object* v_a_2243_ = stack[7].m_obj;
lean_object* v_a_2244_ = stack[8].m_obj;
lean_object* v_res_2247_;
v_res_2247_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(v_x_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
stack->m_obj
 = v_res_2247_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed(lean_object* v_x_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(v_x_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
return v_res_2258_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1(){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2264_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
v___x_2266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1));
v___x_2267_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed), 10, 0);
v___x_2268_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2264_, v___x_2265_, v___x_2266_, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2269_;
v_res_2269_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
stack->m_obj
 = v_res_2269_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___boxed(lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
return v_res_2271_;
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
