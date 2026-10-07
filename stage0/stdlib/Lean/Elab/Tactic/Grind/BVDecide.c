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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(lean_object* v_cfg_8_, lean_object* v_goal_9_, lean_object* v_elaborator_10_, lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg___boxed(lean_object* v_cfg_30_, lean_object* v_goal_31_, lean_object* v_elaborator_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_30_, v_goal_31_, v_elaborator_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(lean_object* v_cfg_37_, lean_object* v_goal_38_, lean_object* v_elaborator_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_37_, v_goal_38_, v_elaborator_39_, v_a_44_, v_a_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___boxed(lean_object* v_cfg_48_, lean_object* v_goal_49_, lean_object* v_elaborator_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig(v_cfg_48_, v_goal_49_, v_elaborator_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_box(0);
v___x_60_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg(){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___closed__0);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg___boxed(lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(lean_object* v_00_u03b1_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___boxed(lean_object* v_00_u03b1_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0(v_00_u03b1_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(lean_object* v_snd_89_, lean_object* v_ref_90_, lean_object* v_a_x3f_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_io_remove_file(v_snd_89_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v_ref_90_);
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_113_; 
v_a_102_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_113_ == 0)
{
v___x_104_ = v___x_93_;
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_93_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_106_ = lean_io_error_to_string(v_a_102_);
v___x_107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
v___x_108_ = l_Lean_MessageData_ofFormat(v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_ref_90_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_109_);
v___x_111_ = v___x_104_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0___boxed(lean_object* v_snd_114_, lean_object* v_ref_115_, lean_object* v_a_x3f_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_114_, v_ref_115_, v_a_x3f_116_);
lean_dec(v_a_x3f_116_);
lean_dec_ref(v_snd_114_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(lean_object* v_f_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_ref_129_; lean_object* v___x_130_; 
v_ref_129_ = lean_ctor_get(v___y_126_, 2);
v___x_130_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v_r_134_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v_fst_132_ = lean_ctor_get(v_a_131_, 0);
lean_inc(v_fst_132_);
v_snd_133_ = lean_ctor_get(v_a_131_, 1);
lean_inc_n(v_snd_133_, 2);
lean_dec(v_a_131_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc_ref(v___y_124_);
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
v_r_134_ = lean_apply_11(v_f_119_, v_fst_132_, v_snd_133_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
if (lean_obj_tag(v_r_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_159_; 
v_a_135_ = lean_ctor_get(v_r_134_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_r_134_);
if (v_isSharedCheck_159_ == 0)
{
v___x_137_ = v_r_134_;
v_isShared_138_ = v_isSharedCheck_159_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v_r_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_159_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
lean_inc(v_a_135_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_158_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
lean_inc(v_ref_129_);
v___x_141_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_133_, v_ref_129_, v___x_140_);
lean_dec_ref(v___x_140_);
lean_dec(v_snd_133_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v___x_141_, 0);
lean_dec(v_unused_149_);
v___x_143_ = v___x_141_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_dec(v___x_141_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v_a_135_);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_135_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
lean_dec(v_a_135_);
v_a_150_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_141_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_141_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_a_160_ = lean_ctor_get(v_r_134_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v_r_134_, 1);
v___x_161_ = lean_box(0);
lean_inc(v_ref_129_);
v___x_162_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___lam__0(v_snd_133_, v_ref_129_, v___x_161_);
lean_dec(v_snd_133_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v___x_162_, 0);
lean_dec(v_unused_170_);
v___x_164_ = v___x_162_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_dec(v___x_162_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 1);
lean_ctor_set(v___x_164_, 0, v_a_160_);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_160_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_a_160_);
v_a_171_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_162_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_162_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_190_; 
lean_dec_ref(v_f_119_);
v_a_179_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_190_ == 0)
{
v___x_181_ = v___x_130_;
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_130_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_183_ = lean_io_error_to_string(v_a_179_);
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
v___x_185_ = l_Lean_MessageData_ofFormat(v___x_184_);
lean_inc(v_ref_129_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_ref_129_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_186_);
v___x_188_ = v___x_181_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg___boxed(lean_object* v_f_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(lean_object* v_00_u03b1_202_, lean_object* v_f_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v_f_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___boxed(lean_object* v_00_u03b1_214_, lean_object* v_f_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1(v_00_u03b1_214_, v_f_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_x_229_, lean_object* v_lratFile_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(v_lratFile_230_, v_a_226_, v_a_227_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_a_228_);
v___x_243_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_bvDecide___boxed), 12, 2);
lean_closure_set(v___x_243_, 0, v___x_242_);
lean_closure_set(v___x_243_, 1, v_a_241_);
v___x_244_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_243_, v___y_231_, v___y_232_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_244_, 1);
v___x_245_ = lean_box(0);
v___x_246_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_245_, v___y_232_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_244_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_a_228_);
v_a_255_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_240_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_240_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed(lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_x_266_, lean_object* v_lratFile_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0(v_a_263_, v_a_264_, v_a_265_, v_x_266_, v_lratFile_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v_x_266_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide(lean_object* v_x_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
lean_inc(v_x_304_);
v___x_315_ = l_Lean_Syntax_isOfKind(v_x_304_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v_x_304_);
v___x_316_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_316_;
}
else
{
lean_object* v___x_317_; lean_object* v_cfg_318_; lean_object* v_types_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v_cfg_318_ = l_Lean_Syntax_getArg(v_x_304_, v___x_317_);
v___x_364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_318_);
v___x_365_ = l_Lean_Syntax_isOfKind(v_cfg_318_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_cfg_318_);
lean_dec(v_x_304_);
v___x_366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_366_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(2u);
v___x_368_ = l_Lean_Syntax_getArg(v_x_304_, v___x_367_);
lean_dec(v_x_304_);
v___x_369_ = l_Lean_Syntax_isNone(v___x_368_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; 
lean_inc(v___x_368_);
v___x_370_ = l_Lean_Syntax_matchesNull(v___x_368_, v___x_317_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v___x_368_);
lean_dec(v_cfg_318_);
v___x_371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v_types_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v_types_373_ = l_Lean_Syntax_getArg(v___x_368_, v___x_372_);
lean_dec(v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_373_);
v___x_377_ = l_Lean_Syntax_isOfKind(v_types_373_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_types_373_);
lean_dec(v_cfg_318_);
v___x_378_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_378_;
}
else
{
goto v___jp_374_;
}
}
else
{
goto v___jp_374_;
}
v___jp_374_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v_types_373_);
v_types_320_ = v___x_375_;
v___y_321_ = v_a_305_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_307_;
v___y_324_ = v_a_308_;
v___y_325_ = v_a_309_;
v___y_326_ = v_a_310_;
v___y_327_ = v_a_311_;
v___y_328_ = v_a_312_;
goto v___jp_319_;
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v___x_368_);
v___x_379_ = lean_box(0);
v_types_320_ = v___x_379_;
v___y_321_ = v_a_305_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_307_;
v___y_324_ = v_a_308_;
v___y_325_ = v_a_309_;
v___y_326_ = v_a_310_;
v___y_327_ = v_a_311_;
v___y_328_ = v_a_312_;
goto v___jp_319_;
}
}
v___jp_319_:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; 
lean_dec_ref_known(v___x_329_, 1);
v___x_330_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_322_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v_mvarId_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v_mvarId_332_ = lean_ctor_get(v_a_331_, 1);
v___x_333_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__7));
lean_inc(v_mvarId_332_);
v___x_334_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_318_, v_mvarId_332_, v___x_333_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_320_, v_a_335_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___f_338_; lean_object* v___x_339_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v___f_338_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___lam__0___boxed), 14, 3);
lean_closure_set(v___f_338_, 0, v_a_335_);
lean_closure_set(v___f_338_, 1, v_a_337_);
lean_closure_set(v___f_338_, 2, v_a_331_);
v___x_339_ = l_IO_FS_withTempFile___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__1___redArg(v___f_338_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
return v___x_339_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_335_);
lean_dec(v_a_331_);
v_a_340_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_336_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_336_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_a_331_);
lean_dec(v_types_320_);
v_a_348_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_334_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_334_);
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
lean_dec(v_types_320_);
lean_dec(v_cfg_318_);
v_a_356_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_330_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_330_);
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
lean_dec(v_types_320_);
lean_dec(v_cfg_318_);
return v___x_329_;
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
size_t v___x_27066__boxed_622_; lean_object* v_res_623_; 
v___x_27066__boxed_622_ = lean_unbox_usize(v___x_611_);
lean_dec(v___x_611_);
v_res_623_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0(v_a_610_, v___x_27066__boxed_622_, v___x_612_, v___x_613_, v___x_614_, v___x_615_, v_final_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
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
lean_object* v_v_708_; lean_object* v_hyp_709_; lean_object* v_grindProof_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_808_; 
v_v_708_ = lean_array_uget(v_bs_700_, v_i_699_);
v_hyp_709_ = lean_ctor_get(v_v_708_, 0);
v_grindProof_710_ = lean_ctor_get(v_v_708_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_v_708_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_v_708_, 1);
lean_dec(v_unused_809_);
v___x_712_ = v_v_708_;
v_isShared_713_ = v_isSharedCheck_808_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_grindProof_710_);
lean_inc(v_hyp_709_);
lean_dec(v_v_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_808_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_type_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_804_; 
v_type_714_ = lean_ctor_get(v_hyp_709_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_hyp_709_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; 
v_unused_805_ = lean_ctor_get(v_hyp_709_, 3);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_hyp_709_, 2);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_hyp_709_, 0);
lean_dec(v_unused_807_);
v___x_716_ = v_hyp_709_;
v_isShared_717_ = v_isSharedCheck_804_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_type_714_);
lean_dec(v_hyp_709_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_804_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v_bs_x27_719_; lean_object* v_a_721_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v_bs_x27_719_ = lean_array_uset(v_bs_700_, v_i_699_, v___x_718_);
v___x_726_ = lean_box(1);
v___x_727_ = l_Lean_PrettyPrinter_delab(v_type_714_, v___x_726_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
v___x_729_ = lean_apply_5(v_grindProof_710_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, lean_box(0));
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
if (lean_obj_tag(v_a_730_) == 0)
{
lean_object* v_ref_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
lean_del_object(v___x_716_);
v_ref_731_ = lean_ctor_get(v___y_703_, 2);
v___x_732_ = 0;
v___x_733_ = l_Lean_SourceInfo_fromRef(v_ref_731_, v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__1));
v___x_735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
lean_inc_n(v___x_733_, 2);
v___x_736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_733_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 1);
lean_ctor_set(v___x_712_, 2, v___x_738_);
lean_ctor_set(v___x_712_, 1, v___x_737_);
lean_ctor_set(v___x_712_, 0, v___x_733_);
v___x_740_ = v___x_712_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v___x_738_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
lean_inc(v___x_733_);
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_733_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_Syntax_node4(v___x_733_, v___x_734_, v___x_736_, v___x_740_, v___x_742_, v_a_728_);
v_a_721_ = v___x_743_;
goto v___jp_720_;
}
}
else
{
lean_object* v_toCold_745_; lean_object* v_val_746_; lean_object* v_ref_747_; lean_object* v_quotContext_748_; lean_object* v_currMacroScope_749_; uint8_t v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v_toCold_745_ = lean_ctor_get(v___y_703_, 0);
v_val_746_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v_a_730_, 1);
v_ref_747_ = lean_ctor_get(v___y_703_, 2);
v_quotContext_748_ = lean_ctor_get(v_toCold_745_, 8);
v_currMacroScope_749_ = lean_ctor_get(v_toCold_745_, 9);
v___x_750_ = 0;
v___x_751_ = l_Lean_SourceInfo_fromRef(v_ref_747_, v___x_750_);
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__2));
v___x_753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__4));
lean_inc_n(v___x_751_, 2);
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_751_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__7));
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__9));
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__11));
v___x_758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__13));
v___x_759_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__14);
v___x_760_ = lean_box(0);
lean_inc(v_currMacroScope_749_);
lean_inc(v_quotContext_748_);
v___x_761_ = l_Lean_addMacroScope(v_quotContext_748_, v___x_760_, v_currMacroScope_749_);
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__21));
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 3);
lean_ctor_set(v___x_716_, 3, v___x_762_);
lean_ctor_set(v___x_716_, 2, v___x_761_);
lean_ctor_set(v___x_716_, 1, v___x_759_);
lean_ctor_set(v___x_716_, 0, v___x_751_);
v___x_764_ = v___x_716_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v___x_762_);
v___x_764_ = v_reuseFailAlloc_786_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
lean_inc_n(v___x_751_, 3);
v___x_765_ = l_Lean_Syntax_node1(v___x_751_, v___x_758_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___x_751_, v___x_757_, v___x_765_);
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_768_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 1);
lean_ctor_set(v___x_712_, 2, v___x_768_);
lean_ctor_set(v___x_712_, 1, v___x_767_);
lean_ctor_set(v___x_712_, 0, v___x_751_);
v___x_770_ = v___x_712_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v___x_768_);
v___x_770_ = v_reuseFailAlloc_785_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__23));
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__3));
lean_inc_n(v___x_751_, 8);
v___x_773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_751_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_Syntax_node2(v___x_751_, v___x_771_, v___x_773_, v_a_728_);
v___x_775_ = l_Lean_Syntax_node1(v___x_751_, v___x_767_, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__24));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_751_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__26));
v___x_779_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___closed__27));
v___x_780_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_751_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Lean_Syntax_node2(v___x_751_, v___x_778_, v___x_780_, v_val_746_);
v___x_782_ = l_Lean_Syntax_node5(v___x_751_, v___x_756_, v___x_766_, v___x_770_, v___x_775_, v___x_777_, v___x_781_);
v___x_783_ = l_Lean_Syntax_node1(v___x_751_, v___x_755_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node2(v___x_751_, v___x_753_, v___x_754_, v___x_783_);
v_a_721_ = v___x_784_;
goto v___jp_720_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_728_);
lean_dec_ref(v_bs_x27_719_);
lean_del_object(v___x_716_);
lean_del_object(v___x_712_);
v_a_787_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_729_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_729_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_del_object(v___x_716_);
lean_del_object(v___x_712_);
lean_dec_ref(v_grindProof_710_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_727_, 1);
v_a_721_ = v_a_795_;
goto v___jp_720_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_bs_x27_719_);
v_a_796_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_727_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_727_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
v___jp_720_:
{
size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_699_, v___x_722_);
v___x_724_ = lean_array_uset(v_bs_x27_719_, v_i_699_, v_a_721_);
v_i_699_ = v___x_723_;
v_bs_700_ = v___x_724_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg___boxed(lean_object* v_sz_810_, lean_object* v_i_811_, lean_object* v_bs_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
size_t v_sz_boxed_818_; size_t v_i_boxed_819_; lean_object* v_res_820_; 
v_sz_boxed_818_ = lean_unbox_usize(v_sz_810_);
lean_dec(v_sz_810_);
v_i_boxed_819_ = lean_unbox_usize(v_i_811_);
lean_dec(v_i_811_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_boxed_818_, v_i_boxed_819_, v_bs_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(size_t v_sz_821_, size_t v_i_822_, lean_object* v_bs_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___redArg(v_sz_821_, v_i_822_, v_bs_823_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed(lean_object* v_sz_834_, lean_object* v_i_835_, lean_object* v_bs_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
size_t v_sz_boxed_846_; size_t v_i_boxed_847_; lean_object* v_res_848_; 
v_sz_boxed_846_ = lean_unbox_usize(v_sz_834_);
lean_dec(v_sz_834_);
v_i_boxed_847_ = lean_unbox_usize(v_i_835_);
lean_dec(v_i_835_);
v_res_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0(v_sz_boxed_846_, v_i_boxed_847_, v_bs_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(lean_object* v_x_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_908_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
lean_inc(v_x_886_);
v___x_909_ = l_Lean_Syntax_isOfKind(v_x_886_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v_x_886_);
v___x_910_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v_cfgStx_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v_cfgStx_912_ = l_Lean_Syntax_getArg(v_x_886_, v___x_911_);
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_912_);
v___x_914_ = l_Lean_Syntax_isOfKind(v_cfgStx_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_cfgStx_912_);
lean_dec(v_x_886_);
v___x_915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_915_;
}
else
{
lean_object* v___x_916_; lean_object* v_tk_917_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v_typesStx_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_916_ = lean_unsigned_to_nat(0u);
v_tk_917_ = l_Lean_Syntax_getArg(v_x_886_, v___x_916_);
v___x_1163_ = lean_unsigned_to_nat(2u);
v___x_1164_ = l_Lean_Syntax_getArg(v_x_886_, v___x_1163_);
lean_dec(v_x_886_);
v___x_1165_ = l_Lean_Syntax_isNone(v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; 
lean_inc(v___x_1164_);
v___x_1166_ = l_Lean_Syntax_matchesNull(v___x_1164_, v___x_911_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
lean_dec(v___x_1164_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v___x_1167_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1167_;
}
else
{
lean_object* v_typesStx_1168_; 
v_typesStx_1168_ = l_Lean_Syntax_getArg(v___x_1164_, v___x_916_);
lean_dec(v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1168_);
v___x_1172_ = l_Lean_Syntax_isOfKind(v_typesStx_1168_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_dec(v_typesStx_1168_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v___x_1173_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1173_;
}
else
{
goto v___jp_1169_;
}
}
else
{
goto v___jp_1169_;
}
v___jp_1169_:
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_typesStx_1168_);
v_typesStx_1030_ = v___x_1170_;
v___y_1031_ = v_a_887_;
v___y_1032_ = v_a_888_;
v___y_1033_ = v_a_889_;
v___y_1034_ = v_a_890_;
v___y_1035_ = v_a_891_;
v___y_1036_ = v_a_892_;
v___y_1037_ = v_a_893_;
v___y_1038_ = v_a_894_;
goto v___jp_1029_;
}
}
}
else
{
lean_object* v___x_1174_; 
lean_dec(v___x_1164_);
v___x_1174_ = lean_box(0);
v_typesStx_1030_ = v___x_1174_;
v___y_1031_ = v_a_887_;
v___y_1032_ = v_a_888_;
v___y_1033_ = v_a_889_;
v___y_1034_ = v_a_890_;
v___y_1035_ = v_a_891_;
v___y_1036_ = v_a_892_;
v___y_1037_ = v_a_893_;
v___y_1038_ = v_a_894_;
goto v___jp_1029_;
}
v___jp_918_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_inc_ref(v___y_920_);
v___x_932_ = l_Array_append___redArg(v___y_920_, v___y_931_);
lean_dec_ref(v___y_931_);
lean_inc(v___y_922_);
lean_inc(v___y_919_);
v___x_933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_933_, 0, v___y_919_);
lean_ctor_set(v___x_933_, 1, v___y_922_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
lean_inc(v___y_928_);
v___x_934_ = l_Lean_Syntax_node3(v___y_919_, v___y_928_, v___y_921_, v_cfgStx_912_, v___x_933_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_923_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_927_);
v___x_935_ = lean_apply_6(v___y_929_, v___x_934_, v___y_927_, v___y_925_, v___y_923_, v___y_930_, lean_box(0));
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_a_936_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
lean_ctor_set(v___x_940_, 2, v___x_939_);
lean_ctor_set(v___x_940_, 3, v___x_939_);
lean_ctor_set(v___x_940_, 4, v___x_939_);
lean_ctor_set(v___x_940_, 5, v___x_939_);
lean_inc(v___y_924_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v___y_924_);
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_943_ = 4;
v___x_944_ = l_Lean_MessageData_nil;
v___x_945_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_917_, v___x_940_, v___x_941_, v___x_942_, v___x_939_, v___x_943_, v___x_944_, v___y_923_, v___y_930_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_dec_ref_known(v___x_945_, 1);
v___y_897_ = v___y_926_;
v___y_898_ = v___y_927_;
v___y_899_ = v___y_925_;
v___y_900_ = v___y_923_;
v___y_901_ = v___y_930_;
goto v___jp_896_;
}
else
{
return v___x_945_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_tk_917_);
v_a_946_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_935_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_935_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
v___jp_954_:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_inc_ref(v___y_959_);
v___x_969_ = l_Array_append___redArg(v___y_959_, v___y_968_);
lean_dec_ref(v___y_968_);
lean_inc(v___y_964_);
lean_inc(v___y_958_);
v___x_970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_970_, 0, v___y_958_);
lean_ctor_set(v___x_970_, 1, v___y_964_);
lean_ctor_set(v___x_970_, 2, v___x_969_);
v___x_971_ = lean_box(2);
v___x_972_ = l_Lean_Syntax_mkStrLit(v___y_956_, v___x_971_);
lean_inc(v___y_955_);
v___x_973_ = l_Lean_Syntax_node4(v___y_958_, v___y_955_, v___y_963_, v_cfgStx_912_, v___x_970_, v___x_972_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_962_);
lean_inc_ref(v___y_965_);
v___x_974_ = lean_apply_6(v___y_966_, v___x_973_, v___y_965_, v___y_962_, v___y_957_, v___y_967_, lean_box(0));
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref_known(v___x_974_, 1);
v___x_976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v_a_975_);
v___x_978_ = lean_box(0);
v___x_979_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
lean_ctor_set(v___x_979_, 3, v___x_978_);
lean_ctor_set(v___x_979_, 4, v___x_978_);
lean_ctor_set(v___x_979_, 5, v___x_978_);
lean_inc(v___y_960_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___y_960_);
v___x_981_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_982_ = 4;
v___x_983_ = l_Lean_MessageData_nil;
v___x_984_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_917_, v___x_979_, v___x_980_, v___x_981_, v___x_978_, v___x_982_, v___x_983_, v___y_957_, v___y_967_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec_ref_known(v___x_984_, 1);
v___y_897_ = v___y_961_;
v___y_898_ = v___y_965_;
v___y_899_ = v___y_962_;
v___y_900_ = v___y_957_;
v___y_901_ = v___y_967_;
goto v___jp_896_;
}
else
{
return v___x_984_;
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_tk_917_);
v_a_985_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_974_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_974_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
v___jp_993_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_inc_ref(v___y_1000_);
v___x_1007_ = l_Array_append___redArg(v___y_1000_, v___y_1006_);
lean_dec_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc(v___y_999_);
v___x_1008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1008_, 0, v___y_999_);
lean_ctor_set(v___x_1008_, 1, v___y_1005_);
lean_ctor_set(v___x_1008_, 2, v___x_1007_);
lean_inc(v___y_994_);
v___x_1009_ = l_Lean_Syntax_node3(v___y_999_, v___y_994_, v___y_1004_, v_cfgStx_912_, v___x_1008_);
lean_inc(v___y_1003_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_1001_);
v___x_1010_ = lean_apply_6(v___y_1002_, v___x_1009_, v___y_1001_, v___y_996_, v___y_995_, v___y_1003_, lean_box(0));
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__2));
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_a_1011_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
lean_ctor_set(v___x_1015_, 2, v___x_1014_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
lean_ctor_set(v___x_1015_, 4, v___x_1014_);
lean_ctor_set(v___x_1015_, 5, v___x_1014_);
lean_inc(v___y_998_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___y_998_);
v___x_1017_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1018_ = 4;
v___x_1019_ = l_Lean_MessageData_nil;
v___x_1020_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_917_, v___x_1015_, v___x_1016_, v___x_1017_, v___x_1014_, v___x_1018_, v___x_1019_, v___y_995_, v___y_1003_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_dec_ref_known(v___x_1020_, 1);
v___y_897_ = v___y_997_;
v___y_898_ = v___y_1001_;
v___y_899_ = v___y_996_;
v___y_900_ = v___y_995_;
v___y_901_ = v___y_1003_;
goto v___jp_896_;
}
else
{
return v___x_1020_;
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_tk_917_);
v_a_1021_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1010_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1010_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
v___jp_1029_:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1161_; 
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v___x_1039_, 0);
lean_dec(v_unused_1162_);
v___x_1041_ = v___x_1039_;
v_isShared_1042_ = v_isSharedCheck_1161_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v___x_1039_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1161_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1032_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v_mvarId_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v_mvarId_1045_ = lean_ctor_get(v_a_1044_, 1);
lean_inc_n(v_mvarId_1045_, 2);
v___x_1046_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__5));
lean_inc(v_cfgStx_912_);
v___x_1047_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_912_, v_mvarId_1045_, v___x_1046_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
lean_inc(v_typesStx_1030_);
v___x_1049_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1030_, v_a_1048_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_mkContext(v_a_1048_, v_a_1050_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 1);
lean_ctor_set(v___x_1041_, 0, v_a_1044_);
v___x_1054_ = v___x_1041_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1044_);
v___x_1054_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed), 12, 2);
lean_closure_set(v___x_1055_, 0, v___x_1054_);
lean_closure_set(v___x_1055_, 1, v_a_1052_);
v___x_1056_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1055_, v___y_1031_, v___y_1032_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v_lemmas_1058_; lean_object* v_action_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1119_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v_lemmas_1058_ = lean_ctor_get(v_a_1057_, 0);
v_action_1059_ = lean_ctor_get(v_a_1057_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_a_1057_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1061_ = v_a_1057_;
v_isShared_1062_ = v_isSharedCheck_1119_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_action_1059_);
lean_inc(v_lemmas_1058_);
lean_dec(v_a_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1119_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
size_t v_sz_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_sz_1063_ = lean_array_size(v_lemmas_1058_);
v___x_1064_ = lean_box_usize(v_sz_1063_);
v___x_1065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___x_1066_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__0___boxed), 12, 3);
lean_closure_set(v___x_1066_, 0, v___x_1064_);
lean_closure_set(v___x_1066_, 1, v___x_1065_);
lean_closure_set(v___x_1066_, 2, v_lemmas_1058_);
v___x_1067_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__1___redArg(v_mvarId_1045_, v___x_1066_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed__const__1));
v___f_1070_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___boxed), 12, 6);
lean_closure_set(v___f_1070_, 0, v_a_1068_);
lean_closure_set(v___f_1070_, 1, v___x_1069_);
lean_closure_set(v___f_1070_, 2, v___x_904_);
lean_closure_set(v___f_1070_, 3, v___x_905_);
lean_closure_set(v___f_1070_, 4, v___x_906_);
lean_closure_set(v___f_1070_, 5, v___x_907_);
switch(lean_obj_tag(v_action_1059_))
{
case 0:
{
lean_object* v_ref_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v_ref_1071_ = lean_ctor_get(v___y_1037_, 2);
v___x_1072_ = 0;
v___x_1073_ = l_Lean_SourceInfo_fromRef(v_ref_1071_, v___x_1072_);
v___x_1074_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_1075_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1073_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 2);
lean_ctor_set(v___x_1061_, 1, v___x_1075_);
lean_ctor_set(v___x_1061_, 0, v___x_1073_);
v___x_1077_ = v___x_1061_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1030_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1081_; 
v_val_1080_ = lean_ctor_get(v_typesStx_1030_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v_typesStx_1030_, 1);
v___x_1081_ = l_Array_mkArray1___redArg(v_val_1080_);
v___y_994_ = v___x_1074_;
v___y_995_ = v___y_1037_;
v___y_996_ = v___y_1036_;
v___y_997_ = v___y_1032_;
v___y_998_ = v_ref_1071_;
v___y_999_ = v___x_1073_;
v___y_1000_ = v___x_1079_;
v___y_1001_ = v___y_1035_;
v___y_1002_ = v___f_1070_;
v___y_1003_ = v___y_1038_;
v___y_1004_ = v___x_1077_;
v___y_1005_ = v___x_1078_;
v___y_1006_ = v___x_1081_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_typesStx_1030_);
v___x_1082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_994_ = v___x_1074_;
v___y_995_ = v___y_1037_;
v___y_996_ = v___y_1036_;
v___y_997_ = v___y_1032_;
v___y_998_ = v_ref_1071_;
v___y_999_ = v___x_1073_;
v___y_1000_ = v___x_1079_;
v___y_1001_ = v___y_1035_;
v___y_1002_ = v___f_1070_;
v___y_1003_ = v___y_1038_;
v___y_1004_ = v___x_1077_;
v___y_1005_ = v___x_1078_;
v___y_1006_ = v___x_1082_;
goto v___jp_993_;
}
}
}
case 1:
{
lean_object* v_path_1084_; lean_object* v_ref_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_path_1084_ = lean_ctor_get(v_action_1059_, 0);
lean_inc_ref(v_path_1084_);
lean_dec_ref_known(v_action_1059_, 1);
v_ref_1085_ = lean_ctor_get(v___y_1037_, 2);
v___x_1086_ = 0;
v___x_1087_ = l_Lean_SourceInfo_fromRef(v_ref_1085_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__12));
lean_inc(v___x_1087_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 2);
lean_ctor_set(v___x_1061_, 1, v___x_1089_);
lean_ctor_set(v___x_1061_, 0, v___x_1087_);
v___x_1091_ = v___x_1061_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1093_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1030_) == 1)
{
lean_object* v_val_1094_; lean_object* v___x_1095_; 
v_val_1094_ = lean_ctor_get(v_typesStx_1030_, 0);
lean_inc(v_val_1094_);
lean_dec_ref_known(v_typesStx_1030_, 1);
v___x_1095_ = l_Array_mkArray1___redArg(v_val_1094_);
v___y_955_ = v___x_1088_;
v___y_956_ = v_path_1084_;
v___y_957_ = v___y_1037_;
v___y_958_ = v___x_1087_;
v___y_959_ = v___x_1093_;
v___y_960_ = v_ref_1085_;
v___y_961_ = v___y_1032_;
v___y_962_ = v___y_1036_;
v___y_963_ = v___x_1091_;
v___y_964_ = v___x_1092_;
v___y_965_ = v___y_1035_;
v___y_966_ = v___f_1070_;
v___y_967_ = v___y_1038_;
v___y_968_ = v___x_1095_;
goto v___jp_954_;
}
else
{
lean_object* v___x_1096_; 
lean_dec(v_typesStx_1030_);
v___x_1096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_955_ = v___x_1088_;
v___y_956_ = v_path_1084_;
v___y_957_ = v___y_1037_;
v___y_958_ = v___x_1087_;
v___y_959_ = v___x_1093_;
v___y_960_ = v_ref_1085_;
v___y_961_ = v___y_1032_;
v___y_962_ = v___y_1036_;
v___y_963_ = v___x_1091_;
v___y_964_ = v___x_1092_;
v___y_965_ = v___y_1035_;
v___y_966_ = v___f_1070_;
v___y_967_ = v___y_1038_;
v___y_968_ = v___x_1096_;
goto v___jp_954_;
}
}
}
default: 
{
lean_object* v_ref_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_ref_1098_ = lean_ctor_get(v___y_1037_, 2);
v___x_1099_ = 0;
v___x_1100_ = l_Lean_SourceInfo_fromRef(v_ref_1098_, v___x_1099_);
v___x_1101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__5));
v___x_1102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__6));
lean_inc(v___x_1100_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 2);
lean_ctor_set(v___x_1061_, 1, v___x_1102_);
lean_ctor_set(v___x_1061_, 0, v___x_1100_);
v___x_1104_ = v___x_1061_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1106_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1030_) == 1)
{
lean_object* v_val_1107_; lean_object* v___x_1108_; 
v_val_1107_ = lean_ctor_get(v_typesStx_1030_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v_typesStx_1030_, 1);
v___x_1108_ = l_Array_mkArray1___redArg(v_val_1107_);
v___y_919_ = v___x_1100_;
v___y_920_ = v___x_1106_;
v___y_921_ = v___x_1104_;
v___y_922_ = v___x_1105_;
v___y_923_ = v___y_1037_;
v___y_924_ = v_ref_1098_;
v___y_925_ = v___y_1036_;
v___y_926_ = v___y_1032_;
v___y_927_ = v___y_1035_;
v___y_928_ = v___x_1101_;
v___y_929_ = v___f_1070_;
v___y_930_ = v___y_1038_;
v___y_931_ = v___x_1108_;
goto v___jp_918_;
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_typesStx_1030_);
v___x_1109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__9));
v___y_919_ = v___x_1100_;
v___y_920_ = v___x_1106_;
v___y_921_ = v___x_1104_;
v___y_922_ = v___x_1105_;
v___y_923_ = v___y_1037_;
v___y_924_ = v_ref_1098_;
v___y_925_ = v___y_1036_;
v___y_926_ = v___y_1032_;
v___y_927_ = v___y_1035_;
v___y_928_ = v___x_1101_;
v___y_929_ = v___f_1070_;
v___y_930_ = v___y_1038_;
v___y_931_ = v___x_1109_;
goto v___jp_918_;
}
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_del_object(v___x_1061_);
lean_dec(v_action_1059_);
lean_dec(v_typesStx_1030_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v_a_1111_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1067_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1067_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_mvarId_1045_);
lean_dec(v_typesStx_1030_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v_a_1120_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1056_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1056_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_mvarId_1045_);
lean_dec(v_a_1044_);
lean_del_object(v___x_1041_);
lean_dec(v_typesStx_1030_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v_a_1129_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1051_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1051_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_a_1048_);
lean_dec(v_mvarId_1045_);
lean_dec(v_a_1044_);
lean_del_object(v___x_1041_);
lean_dec(v_typesStx_1030_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v_a_1137_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1049_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1049_);
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
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_mvarId_1045_);
lean_dec(v_a_1044_);
lean_del_object(v___x_1041_);
lean_dec(v_typesStx_1030_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v_a_1145_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1047_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1047_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_del_object(v___x_1041_);
lean_dec(v_typesStx_1030_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
v_a_1153_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1043_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1043_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
else
{
lean_dec(v_typesStx_1030_);
lean_dec(v_tk_917_);
lean_dec(v_cfgStx_912_);
return v___x_1039_;
}
}
}
}
v___jp_896_:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_box(0);
v___x_903_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_902_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed(lean_object* v_x_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace(v_x_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(size_t v_sz_1186_, size_t v_i_1187_, lean_object* v_bs_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg(v_sz_1186_, v_i_1187_, v_bs_1188_, v___y_1191_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___boxed(lean_object* v_sz_1195_, lean_object* v_i_1196_, lean_object* v_bs_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
size_t v_sz_boxed_1203_; size_t v_i_boxed_1204_; lean_object* v_res_1205_; 
v_sz_boxed_1203_ = lean_unbox_usize(v_sz_1195_);
lean_dec(v_sz_1195_);
v_i_boxed_1204_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_res_1205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2(v_sz_boxed_1203_, v_i_boxed_1204_, v_bs_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1(){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1211_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__1));
v___x_1213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___closed__1));
v___x_1214_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___boxed), 10, 0);
v___x_1215_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1211_, v___x_1212_, v___x_1213_, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1___boxed(lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace__1();
return v_res_1217_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1218_, lean_object* v_opt_1219_){
_start:
{
lean_object* v_name_1220_; lean_object* v_defValue_1221_; lean_object* v_map_1222_; lean_object* v___x_1223_; 
v_name_1220_ = lean_ctor_get(v_opt_1219_, 0);
v_defValue_1221_ = lean_ctor_get(v_opt_1219_, 1);
v_map_1222_ = lean_ctor_get(v_opts_1218_, 0);
v___x_1223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1222_, v_name_1220_);
if (lean_obj_tag(v___x_1223_) == 0)
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_unbox(v_defValue_1221_);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; 
v_val_1225_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1223_, 1);
if (lean_obj_tag(v_val_1225_) == 1)
{
uint8_t v_v_1226_; 
v_v_1226_ = lean_ctor_get_uint8(v_val_1225_, 0);
lean_dec_ref_known(v_val_1225_, 0);
return v_v_1226_;
}
else
{
uint8_t v___x_1227_; 
lean_dec(v_val_1225_);
v___x_1227_ = lean_unbox(v_defValue_1221_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1228_, lean_object* v_opt_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v_opts_1228_, v_opt_1229_);
lean_dec_ref(v_opt_1229_);
lean_dec_ref(v_opts_1228_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1238_, uint8_t v___y_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 1)
{
lean_object* v_pre_1241_; 
v_pre_1241_ = lean_ctor_get(v_x_1240_, 0);
switch(lean_obj_tag(v_pre_1241_))
{
case 1:
{
lean_object* v_pre_1242_; 
v_pre_1242_ = lean_ctor_get(v_pre_1241_, 0);
switch(lean_obj_tag(v_pre_1242_))
{
case 0:
{
lean_object* v_str_1243_; lean_object* v_str_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_str_1243_ = lean_ctor_get(v_x_1240_, 1);
v_str_1244_ = lean_ctor_get(v_pre_1241_, 1);
v___x_1245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide__1___closed__3));
v___x_1246_ = lean_string_dec_eq(v_str_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1248_ = lean_string_dec_eq(v_str_1244_, v___x_1247_);
if (v___x_1248_ == 0)
{
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1250_ = lean_string_dec_eq(v_str_1243_, v___x_1249_);
if (v___x_1250_ == 0)
{
return v___x_1250_;
}
else
{
return v_suppressElabErrors_1238_;
}
}
}
else
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1252_ = lean_string_dec_eq(v_str_1243_, v___x_1251_);
if (v___x_1252_ == 0)
{
return v___x_1252_;
}
else
{
return v_suppressElabErrors_1238_;
}
}
}
case 1:
{
lean_object* v_pre_1253_; 
v_pre_1253_ = lean_ctor_get(v_pre_1242_, 0);
if (lean_obj_tag(v_pre_1253_) == 0)
{
lean_object* v_str_1254_; lean_object* v_str_1255_; lean_object* v_str_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_str_1254_ = lean_ctor_get(v_x_1240_, 1);
v_str_1255_ = lean_ctor_get(v_pre_1241_, 1);
v_str_1256_ = lean_ctor_get(v_pre_1242_, 1);
v___x_1257_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1258_ = lean_string_dec_eq(v_str_1256_, v___x_1257_);
if (v___x_1258_ == 0)
{
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1260_ = lean_string_dec_eq(v_str_1255_, v___x_1259_);
if (v___x_1260_ == 0)
{
return v___x_1260_;
}
else
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1262_ = lean_string_dec_eq(v_str_1254_, v___x_1261_);
if (v___x_1262_ == 0)
{
return v___x_1262_;
}
else
{
return v_suppressElabErrors_1238_;
}
}
}
}
else
{
return v___y_1239_;
}
}
default: 
{
return v___y_1239_;
}
}
}
case 0:
{
lean_object* v_str_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_str_1263_ = lean_ctor_get(v_x_1240_, 1);
v___x_1264_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1265_ = lean_string_dec_eq(v_str_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
return v___x_1265_;
}
else
{
return v_suppressElabErrors_1238_;
}
}
default: 
{
return v___y_1239_;
}
}
}
else
{
return v___y_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1266_, lean_object* v___y_1267_, lean_object* v_x_1268_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1269_; uint8_t v___y_7540__boxed_1270_; uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_suppressElabErrors_boxed_1269_ = lean_unbox(v_suppressElabErrors_1266_);
v___y_7540__boxed_1270_ = lean_unbox(v___y_1267_);
v_res_1271_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1269_, v___y_7540__boxed_1270_, v_x_1268_);
lean_dec(v_x_1268_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v_env_1280_; uint8_t v___x_1281_; lean_object* v_env_1282_; lean_object* v___x_1283_; lean_object* v_toCold_1284_; lean_object* v_mctx_1285_; lean_object* v_lctx_1286_; lean_object* v_options_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1279_ = lean_st_ref_get(v___y_1277_);
v_env_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_ref(v_env_1280_);
lean_dec(v___x_1279_);
v___x_1281_ = 0;
v_env_1282_ = l_Lean_Environment_setRecordingDeps(v_env_1280_, v___x_1281_);
v___x_1283_ = lean_st_ref_get(v___y_1275_);
v_toCold_1284_ = lean_ctor_get(v___y_1276_, 0);
v_mctx_1285_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_ref(v_mctx_1285_);
lean_dec(v___x_1283_);
v_lctx_1286_ = lean_ctor_get(v___y_1274_, 2);
v_options_1287_ = lean_ctor_get(v_toCold_1284_, 2);
lean_inc_ref(v_options_1287_);
lean_inc_ref(v_lctx_1286_);
v___x_1288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1288_, 0, v_env_1282_);
lean_ctor_set(v___x_1288_, 1, v_mctx_1285_);
lean_ctor_set(v___x_1288_, 2, v_lctx_1286_);
lean_ctor_set(v___x_1288_, 3, v_options_1287_);
v___x_1289_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_msgData_1273_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msgData_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(lean_object* v_ref_1298_, lean_object* v_msgData_1299_, uint8_t v_severity_1300_, uint8_t v_isSilent_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v_toCold_1315_; lean_object* v___y_1316_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; uint8_t v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1382_; uint8_t v___y_1383_; uint8_t v___y_1384_; uint8_t v___x_1395_; uint8_t v___y_1397_; uint8_t v___y_1398_; uint8_t v___y_1399_; uint8_t v___y_1401_; uint8_t v___x_1409_; 
v___x_1395_ = 2;
v___x_1409_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1300_, v___x_1395_);
if (v___x_1409_ == 0)
{
v___y_1401_ = v___x_1409_;
goto v___jp_1400_;
}
else
{
uint8_t v___x_1410_; 
lean_inc_ref(v_msgData_1299_);
v___x_1410_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1299_);
v___y_1401_ = v___x_1410_;
goto v___jp_1400_;
}
v___jp_1307_:
{
lean_object* v_currNamespace_1317_; lean_object* v_openDecls_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v_env_1323_; lean_object* v_nextMacroScope_1324_; lean_object* v_ngen_1325_; lean_object* v_auxDeclNGen_1326_; lean_object* v_traceState_1327_; lean_object* v_cache_1328_; lean_object* v_recordedDeps_1329_; lean_object* v_messages_1330_; lean_object* v_infoState_1331_; lean_object* v_snapshotTasks_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1343_; 
v_currNamespace_1317_ = lean_ctor_get(v_toCold_1315_, 4);
v_openDecls_1318_ = lean_ctor_get(v_toCold_1315_, 5);
lean_inc(v_openDecls_1318_);
lean_inc(v_currNamespace_1317_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_currNamespace_1317_);
lean_ctor_set(v___x_1319_, 1, v_openDecls_1318_);
v___x_1320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___y_1311_);
lean_inc_ref(v___y_1310_);
lean_inc_ref(v___y_1314_);
v___x_1321_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1321_, 0, v___y_1314_);
lean_ctor_set(v___x_1321_, 1, v___y_1313_);
lean_ctor_set(v___x_1321_, 2, v___y_1309_);
lean_ctor_set(v___x_1321_, 3, v___y_1310_);
lean_ctor_set(v___x_1321_, 4, v___x_1320_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*5, v___y_1308_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*5 + 1, v___y_1312_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*5 + 2, v_isSilent_1301_);
v___x_1322_ = lean_st_ref_take(v___y_1316_);
v_env_1323_ = lean_ctor_get(v___x_1322_, 0);
v_nextMacroScope_1324_ = lean_ctor_get(v___x_1322_, 1);
v_ngen_1325_ = lean_ctor_get(v___x_1322_, 2);
v_auxDeclNGen_1326_ = lean_ctor_get(v___x_1322_, 3);
v_traceState_1327_ = lean_ctor_get(v___x_1322_, 4);
v_cache_1328_ = lean_ctor_get(v___x_1322_, 5);
v_recordedDeps_1329_ = lean_ctor_get(v___x_1322_, 6);
v_messages_1330_ = lean_ctor_get(v___x_1322_, 7);
v_infoState_1331_ = lean_ctor_get(v___x_1322_, 8);
v_snapshotTasks_1332_ = lean_ctor_get(v___x_1322_, 9);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1334_ = v___x_1322_;
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snapshotTasks_1332_);
lean_inc(v_infoState_1331_);
lean_inc(v_messages_1330_);
lean_inc(v_recordedDeps_1329_);
lean_inc(v_cache_1328_);
lean_inc(v_traceState_1327_);
lean_inc(v_auxDeclNGen_1326_);
lean_inc(v_ngen_1325_);
lean_inc(v_nextMacroScope_1324_);
lean_inc(v_env_1323_);
lean_dec(v___x_1322_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = l_Lean_MessageLog_add(v___x_1321_, v_messages_1330_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 7, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_env_1323_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_nextMacroScope_1324_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_ngen_1325_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_auxDeclNGen_1326_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_traceState_1327_);
lean_ctor_set(v_reuseFailAlloc_1342_, 5, v_cache_1328_);
lean_ctor_set(v_reuseFailAlloc_1342_, 6, v_recordedDeps_1329_);
lean_ctor_set(v_reuseFailAlloc_1342_, 7, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1342_, 8, v_infoState_1331_);
lean_ctor_set(v_reuseFailAlloc_1342_, 9, v_snapshotTasks_1332_);
v___x_1339_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_st_ref_put(v___y_1316_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1336_);
return v___x_1341_;
}
}
}
v___jp_1344_:
{
lean_object* v_fileName_1353_; lean_object* v_fileMap_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1370_; 
v_fileName_1353_ = lean_ctor_get(v___y_1348_, 0);
v_fileMap_1354_ = lean_ctor_get(v___y_1348_, 1);
v___x_1355_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1299_);
v___x_1356_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v___x_1355_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref_n(v_fileMap_1354_, 2);
v___x_1361_ = l_Lean_FileMap_toPosition(v_fileMap_1354_, v___y_1349_);
lean_dec(v___y_1349_);
v___x_1362_ = l_Lean_FileMap_toPosition(v_fileMap_1354_, v___y_1352_);
lean_dec(v___y_1352_);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___lam__0___closed__2));
if (v___y_1350_ == 0)
{
lean_del_object(v___x_1359_);
lean_dec_ref(v___y_1346_);
v___y_1308_ = v___y_1347_;
v___y_1309_ = v___x_1363_;
v___y_1310_ = v___x_1364_;
v___y_1311_ = v_a_1357_;
v___y_1312_ = v___y_1351_;
v___y_1313_ = v___x_1361_;
v___y_1314_ = v_fileName_1353_;
v_toCold_1315_ = v___y_1345_;
v___y_1316_ = v___y_1305_;
goto v___jp_1307_;
}
else
{
uint8_t v___x_1365_; 
lean_inc(v_a_1357_);
v___x_1365_ = l_Lean_MessageData_hasTag(v___y_1346_, v_a_1357_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec_ref_known(v___x_1363_, 1);
lean_dec_ref(v___x_1361_);
lean_dec(v_a_1357_);
v___x_1366_ = lean_box(0);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1366_);
v___x_1368_ = v___x_1359_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
else
{
lean_del_object(v___x_1359_);
v___y_1308_ = v___y_1347_;
v___y_1309_ = v___x_1363_;
v___y_1310_ = v___x_1364_;
v___y_1311_ = v_a_1357_;
v___y_1312_ = v___y_1351_;
v___y_1313_ = v___x_1361_;
v___y_1314_ = v_fileName_1353_;
v_toCold_1315_ = v___y_1345_;
v___y_1316_ = v___y_1305_;
goto v___jp_1307_;
}
}
}
}
v___jp_1371_:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Syntax_getTailPos_x3f(v___y_1376_, v___y_1375_);
lean_dec(v___y_1376_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_inc(v___y_1378_);
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1372_;
v___y_1349_ = v___y_1378_;
v___y_1350_ = v___y_1373_;
v___y_1351_ = v___y_1377_;
v___y_1352_ = v___y_1378_;
goto v___jp_1344_;
}
else
{
lean_object* v_val_1380_; 
v_val_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___y_1345_ = v___y_1372_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v___y_1375_;
v___y_1348_ = v___y_1372_;
v___y_1349_ = v___y_1378_;
v___y_1350_ = v___y_1373_;
v___y_1351_ = v___y_1377_;
v___y_1352_ = v_val_1380_;
goto v___jp_1344_;
}
}
v___jp_1381_:
{
lean_object* v_toCold_1385_; lean_object* v_ref_1386_; uint8_t v_suppressElabErrors_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v_ref_1391_; lean_object* v___x_1392_; 
v_toCold_1385_ = lean_ctor_get(v___y_1304_, 0);
v_ref_1386_ = lean_ctor_get(v___y_1304_, 2);
v_suppressElabErrors_1387_ = lean_ctor_get_uint8(v___y_1304_, sizeof(void*)*3 + 2);
v___x_1388_ = lean_box(v_suppressElabErrors_1387_);
v___x_1389_ = lean_box(v___y_1382_);
v___f_1390_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1390_, 0, v___x_1388_);
lean_closure_set(v___f_1390_, 1, v___x_1389_);
v_ref_1391_ = l_Lean_replaceRef(v_ref_1298_, v_ref_1386_);
v___x_1392_ = l_Lean_Syntax_getPos_x3f(v_ref_1391_, v___y_1383_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___y_1372_ = v_toCold_1385_;
v___y_1373_ = v_suppressElabErrors_1387_;
v___y_1374_ = v___f_1390_;
v___y_1375_ = v___y_1383_;
v___y_1376_ = v_ref_1391_;
v___y_1377_ = v___y_1384_;
v___y_1378_ = v___x_1393_;
goto v___jp_1371_;
}
else
{
lean_object* v_val_1394_; 
v_val_1394_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v___x_1392_, 1);
v___y_1372_ = v_toCold_1385_;
v___y_1373_ = v_suppressElabErrors_1387_;
v___y_1374_ = v___f_1390_;
v___y_1375_ = v___y_1383_;
v___y_1376_ = v_ref_1391_;
v___y_1377_ = v___y_1384_;
v___y_1378_ = v_val_1394_;
goto v___jp_1371_;
}
}
v___jp_1396_:
{
if (v___y_1399_ == 0)
{
v___y_1382_ = v___y_1397_;
v___y_1383_ = v___y_1398_;
v___y_1384_ = v_severity_1300_;
goto v___jp_1381_;
}
else
{
v___y_1382_ = v___y_1397_;
v___y_1383_ = v___y_1398_;
v___y_1384_ = v___x_1395_;
goto v___jp_1381_;
}
}
v___jp_1400_:
{
if (v___y_1401_ == 0)
{
uint8_t v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = 1;
v___x_1403_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1300_, v___x_1402_);
if (v___x_1403_ == 0)
{
v___y_1397_ = v___y_1401_;
v___y_1398_ = v___y_1401_;
v___y_1399_ = v___x_1403_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1304_);
v___x_1405_ = l_Lean_warningAsError;
v___x_1406_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__3(v___x_1404_, v___x_1405_);
lean_dec_ref(v___x_1404_);
v___y_1397_ = v___y_1401_;
v___y_1398_ = v___y_1401_;
v___y_1399_ = v___x_1406_;
goto v___jp_1396_;
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v_msgData_1299_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1411_, lean_object* v_msgData_1412_, lean_object* v_severity_1413_, lean_object* v_isSilent_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v_severity_boxed_1420_; uint8_t v_isSilent_boxed_1421_; lean_object* v_res_1422_; 
v_severity_boxed_1420_ = lean_unbox(v_severity_1413_);
v_isSilent_boxed_1421_ = lean_unbox(v_isSilent_1414_);
v_res_1422_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1411_, v_msgData_1412_, v_severity_boxed_1420_, v_isSilent_boxed_1421_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v_ref_1411_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(lean_object* v_msgData_1423_, uint8_t v_severity_1424_, uint8_t v_isSilent_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_ref_1431_; lean_object* v___x_1432_; 
v_ref_1431_ = lean_ctor_get(v___y_1428_, 2);
v___x_1432_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1(v_ref_1431_, v_msgData_1423_, v_severity_1424_, v_isSilent_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0___boxed(lean_object* v_msgData_1433_, lean_object* v_severity_1434_, lean_object* v_isSilent_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_severity_boxed_1441_; uint8_t v_isSilent_boxed_1442_; lean_object* v_res_1443_; 
v_severity_boxed_1441_ = lean_unbox(v_severity_1434_);
v_isSilent_boxed_1442_ = lean_unbox(v_isSilent_1435_);
v_res_1443_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1433_, v_severity_boxed_1441_, v_isSilent_boxed_1442_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(lean_object* v_msgData_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = 1;
v___x_1451_ = 0;
v___x_1452_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0(v_msgData_1444_, v___x_1450_, v___x_1451_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0___boxed(lean_object* v_msgData_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v_msgData_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1459_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__2));
v___x_1465_ = l_Lean_stringToMessageData(v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(lean_object* v___x_1466_, lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v_cfgStx_1470_, lean_object* v_tk_1471_, lean_object* v_typesStx_1472_, lean_object* v___x_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_ref_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___y_1490_; 
v_ref_1479_ = lean_ctor_get(v___y_1476_, 2);
v___x_1480_ = 0;
v___x_1481_ = l_Lean_SourceInfo_fromRef(v_ref_1479_, v___x_1480_);
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__1));
v___x_1483_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__6));
v___x_1484_ = l_Lean_Name_mkStr5(v___x_1466_, v___x_1467_, v___x_1468_, v___x_1469_, v___x_1483_);
v___x_1485_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__8));
lean_inc(v___x_1481_);
v___x_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1481_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__3));
v___x_1488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace_spec__2___redArg___closed__4);
if (lean_obj_tag(v_typesStx_1472_) == 1)
{
lean_object* v_val_1511_; lean_object* v___x_1512_; 
v_val_1511_ = lean_ctor_get(v_typesStx_1472_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v_typesStx_1472_, 1);
v___x_1512_ = l_Array_mkArray1___redArg(v_val_1511_);
v___y_1490_ = v___x_1512_;
goto v___jp_1489_;
}
else
{
lean_object* v___x_1513_; 
lean_dec(v_typesStx_1472_);
v___x_1513_ = lean_mk_empty_array_with_capacity(v___x_1473_);
v___y_1490_ = v___x_1513_;
goto v___jp_1489_;
}
v___jp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1491_ = l_Array_append___redArg(v___x_1488_, v___y_1490_);
lean_dec_ref(v___y_1490_);
lean_inc(v___x_1481_);
v___x_1492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1481_);
lean_ctor_set(v___x_1492_, 1, v___x_1487_);
lean_ctor_set(v___x_1492_, 2, v___x_1491_);
v___x_1493_ = l_Lean_Syntax_node3(v___x_1481_, v___x_1484_, v___x_1486_, v_cfgStx_1470_, v___x_1492_);
v___x_1494_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___closed__3);
v___x_1495_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0(v___x_1494_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1509_; 
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v___x_1495_, 0);
lean_dec(v_unused_1510_);
v___x_1497_ = v___x_1495_;
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1495_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1482_);
lean_ctor_set(v___x_1499_, 1, v___x_1493_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
lean_ctor_set(v___x_1501_, 2, v___x_1500_);
lean_ctor_set(v___x_1501_, 3, v___x_1500_);
lean_ctor_set(v___x_1501_, 4, v___x_1500_);
lean_ctor_set(v___x_1501_, 5, v___x_1500_);
lean_inc(v_ref_1479_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 1);
lean_ctor_set(v___x_1497_, 0, v_ref_1479_);
v___x_1503_ = v___x_1497_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_ref_1479_);
v___x_1503_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__3));
v___x_1505_ = 4;
v___x_1506_ = l_Lean_MessageData_nil;
v___x_1507_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_tk_1471_, v___x_1501_, v___x_1503_, v___x_1504_, v___x_1500_, v___x_1505_, v___x_1506_, v___y_1476_, v___y_1477_);
return v___x_1507_;
}
}
}
else
{
lean_dec(v___x_1493_);
lean_dec(v_tk_1471_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed(lean_object* v___x_1514_, lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v___x_1517_, lean_object* v_cfgStx_1518_, lean_object* v_tk_1519_, lean_object* v_typesStx_1520_, lean_object* v___x_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0(v___x_1514_, v___x_1515_, v___x_1516_, v___x_1517_, v_cfgStx_1518_, v_tk_1519_, v_typesStx_1520_, v___x_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___x_1521_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(lean_object* v_x_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__0));
v___x_1544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__1));
v___x_1545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__2));
v___x_1546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__3));
v___x_1547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
lean_inc(v_x_1533_);
v___x_1548_ = l_Lean_Syntax_isOfKind(v_x_1533_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec(v_x_1533_);
v___x_1549_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v_cfgStx_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v_cfgStx_1551_ = l_Lean_Syntax_getArg(v_x_1533_, v___x_1550_);
v___x_1552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfgStx_1551_);
v___x_1553_ = l_Lean_Syntax_isOfKind(v_cfgStx_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v_cfgStx_1551_);
lean_dec(v_x_1533_);
v___x_1554_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v_tk_1556_; lean_object* v_typesStx_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v_tk_1556_ = l_Lean_Syntax_getArg(v_x_1533_, v___x_1555_);
v___x_1629_ = lean_unsigned_to_nat(2u);
v___x_1630_ = l_Lean_Syntax_getArg(v_x_1533_, v___x_1629_);
v___x_1631_ = l_Lean_Syntax_isNone(v___x_1630_);
if (v___x_1631_ == 0)
{
uint8_t v___x_1632_; 
lean_inc(v___x_1630_);
v___x_1632_ = l_Lean_Syntax_matchesNull(v___x_1630_, v___x_1550_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; 
lean_dec(v___x_1630_);
lean_dec(v_tk_1556_);
lean_dec(v_cfgStx_1551_);
lean_dec(v_x_1533_);
v___x_1633_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1633_;
}
else
{
lean_object* v_typesStx_1634_; 
v_typesStx_1634_ = l_Lean_Syntax_getArg(v___x_1630_, v___x_1555_);
lean_dec(v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_typesStx_1634_);
v___x_1638_ = l_Lean_Syntax_isOfKind(v_typesStx_1634_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec(v_typesStx_1634_);
lean_dec(v_tk_1556_);
lean_dec(v_cfgStx_1551_);
lean_dec(v_x_1533_);
v___x_1639_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1639_;
}
else
{
goto v___jp_1635_;
}
}
else
{
goto v___jp_1635_;
}
v___jp_1635_:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_typesStx_1634_);
v_typesStx_1558_ = v___x_1636_;
v___y_1559_ = v_a_1534_;
v___y_1560_ = v_a_1535_;
v___y_1561_ = v_a_1536_;
v___y_1562_ = v_a_1537_;
v___y_1563_ = v_a_1538_;
v___y_1564_ = v_a_1539_;
v___y_1565_ = v_a_1540_;
v___y_1566_ = v_a_1541_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1640_; 
lean_dec(v___x_1630_);
v___x_1640_ = lean_box(0);
v_typesStx_1558_ = v___x_1640_;
v___y_1559_ = v_a_1534_;
v___y_1560_ = v_a_1535_;
v___y_1561_ = v_a_1536_;
v___y_1562_ = v_a_1537_;
v___y_1563_ = v_a_1538_;
v___y_1564_ = v_a_1539_;
v___y_1565_ = v_a_1540_;
v___y_1566_ = v_a_1541_;
goto v___jp_1557_;
}
v___jp_1557_:
{
lean_object* v___x_1567_; lean_object* v_path_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1567_ = lean_unsigned_to_nat(3u);
v_path_1568_ = l_Lean_Syntax_getArg(v_x_1533_, v___x_1567_);
lean_dec(v_x_1533_);
v___x_1569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__1));
lean_inc(v_path_1568_);
v___x_1570_ = l_Lean_Syntax_isOfKind(v_path_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_dec(v_path_1568_);
lean_dec(v_typesStx_1558_);
lean_dec(v_tk_1556_);
lean_dec(v_cfgStx_1551_);
v___x_1571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1571_;
}
else
{
lean_object* v___f_1572_; lean_object* v___x_1573_; 
lean_inc(v_typesStx_1558_);
lean_inc(v_cfgStx_1551_);
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1572_, 0, v___x_1543_);
lean_closure_set(v___f_1572_, 1, v___x_1544_);
lean_closure_set(v___f_1572_, 2, v___x_1545_);
lean_closure_set(v___f_1572_, 3, v___x_1546_);
lean_closure_set(v___f_1572_, 4, v_cfgStx_1551_);
lean_closure_set(v___f_1572_, 5, v_tk_1556_);
lean_closure_set(v___f_1572_, 6, v_typesStx_1558_);
lean_closure_set(v___f_1572_, 7, v___x_1555_);
v___x_1573_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1627_; 
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v___x_1573_, 0);
lean_dec(v_unused_1628_);
v___x_1575_ = v___x_1573_;
v_isShared_1576_ = v_isSharedCheck_1627_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v___x_1573_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1627_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1560_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v_mvarId_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v_mvarId_1579_ = lean_ctor_get(v_a_1578_, 1);
v___x_1580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___closed__2));
lean_inc(v_mvarId_1579_);
v___x_1581_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfgStx_1551_, v_mvarId_1579_, v___x_1580_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_typesStx_1558_, v_a_1582_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = l_Lean_TSyntax_getString(v_path_1568_);
lean_dec(v_path_1568_);
v___x_1586_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(v___x_1585_, v_a_1582_, v_a_1584_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 1);
lean_ctor_set(v___x_1575_, 0, v_a_1578_);
v___x_1589_ = v___x_1575_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1578_);
v___x_1589_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed), 13, 3);
lean_closure_set(v___x_1590_, 0, v___x_1589_);
lean_closure_set(v___x_1590_, 1, v_a_1587_);
lean_closure_set(v___x_1590_, 2, v___f_1572_);
v___x_1591_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_1590_, v___y_1559_, v___y_1560_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref_known(v___x_1591_, 1);
v___x_1592_ = lean_box(0);
v___x_1593_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1592_, v___y_1560_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
return v___x_1593_;
}
else
{
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1578_);
lean_del_object(v___x_1575_);
lean_dec_ref(v___f_1572_);
v_a_1595_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1586_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1586_);
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
lean_dec(v_a_1582_);
lean_dec(v_a_1578_);
lean_del_object(v___x_1575_);
lean_dec_ref(v___f_1572_);
lean_dec(v_path_1568_);
v_a_1603_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1583_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1583_);
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
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_a_1578_);
lean_del_object(v___x_1575_);
lean_dec_ref(v___f_1572_);
lean_dec(v_path_1568_);
lean_dec(v_typesStx_1558_);
v_a_1611_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1581_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1581_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_del_object(v___x_1575_);
lean_dec_ref(v___f_1572_);
lean_dec(v_path_1568_);
lean_dec(v_typesStx_1558_);
lean_dec(v_cfgStx_1551_);
v_a_1619_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1577_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1577_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_1572_);
lean_dec(v_path_1568_);
lean_dec(v_typesStx_1558_);
lean_dec(v_cfgStx_1551_);
return v___x_1573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed(lean_object* v_x_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck(v_x_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1(){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1657_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_1658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__11));
v___x_1659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___closed__1));
v___x_1660_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___boxed), 10, 0);
v___x_1661_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1657_, v___x_1658_, v___x_1659_, v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1___boxed(lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck__1();
return v_res_1663_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1664_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__0);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__1);
v___x_1668_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
lean_ctor_set(v___x_1668_, 2, v___x_1667_);
lean_ctor_set(v___x_1668_, 3, v___x_1667_);
return v___x_1668_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_unsigned_to_nat(16u);
v___x_1671_ = lean_mk_array(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__3);
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v___x_1672_);
return v___x_1674_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__4);
v___x_1676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
lean_ctor_set(v___x_1676_, 2, v___x_1675_);
lean_ctor_set(v___x_1676_, 3, v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(lean_object* v___x_1679_, lean_object* v___x_1680_, lean_object* v___x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1692_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_1693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_1694_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_1695_ = 0;
v___x_1696_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1696_, 0, v___x_1692_);
lean_ctor_set(v___x_1696_, 1, v___x_1693_);
lean_ctor_set(v___x_1696_, 2, v___x_1679_);
lean_ctor_set(v___x_1696_, 3, v___x_1694_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*4, v___x_1695_);
v___x_1697_ = lean_st_mk_ref(v___x_1696_);
v___x_1698_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1680_, v___x_1681_, v___x_1697_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1703_ = lean_st_ref_get(v___x_1697_);
lean_dec(v___x_1697_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_a_1699_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v___x_1697_);
v_a_1709_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1698_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1698_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed(lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v___x_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0(v___x_1717_, v___x_1718_, v___x_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___x_1719_);
lean_dec(v___x_1718_);
return v_res_1730_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_1731_, lean_object* v_i_1732_, lean_object* v_k_1733_){
_start:
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = lean_array_get_size(v_keys_1731_);
v___x_1735_ = lean_nat_dec_lt(v_i_1732_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_dec(v_i_1732_);
return v___x_1735_;
}
else
{
lean_object* v_k_x27_1736_; uint8_t v___x_1737_; 
v_k_x27_1736_ = lean_array_fget_borrowed(v_keys_1731_, v_i_1732_);
v___x_1737_ = l_Lean_instBEqMVarId_beq(v_k_1733_, v_k_x27_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1732_, v___x_1738_);
lean_dec(v_i_1732_);
v_i_1732_ = v___x_1739_;
goto _start;
}
else
{
lean_dec(v_i_1732_);
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_1741_, lean_object* v_i_1742_, lean_object* v_k_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_1741_, v_i_1742_, v_k_1743_);
lean_dec(v_k_1743_);
lean_dec_ref(v_keys_1741_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1746_, size_t v_x_1747_, lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1746_) == 0)
{
lean_object* v_es_1749_; lean_object* v___x_1750_; size_t v___x_1751_; size_t v___x_1752_; lean_object* v_j_1753_; lean_object* v___x_1754_; 
v_es_1749_ = lean_ctor_get(v_x_1746_, 0);
v___x_1750_ = lean_box(2);
v___x_1751_ = ((size_t)31ULL);
v___x_1752_ = lean_usize_land(v_x_1747_, v___x_1751_);
v_j_1753_ = lean_usize_to_nat(v___x_1752_);
v___x_1754_ = lean_array_get_borrowed(v___x_1750_, v_es_1749_, v_j_1753_);
lean_dec(v_j_1753_);
switch(lean_obj_tag(v___x_1754_))
{
case 0:
{
lean_object* v_key_1755_; uint8_t v___x_1756_; 
v_key_1755_ = lean_ctor_get(v___x_1754_, 0);
v___x_1756_ = l_Lean_instBEqMVarId_beq(v_x_1748_, v_key_1755_);
return v___x_1756_;
}
case 1:
{
lean_object* v_node_1757_; size_t v___x_1758_; size_t v___x_1759_; 
v_node_1757_ = lean_ctor_get(v___x_1754_, 0);
v___x_1758_ = ((size_t)5ULL);
v___x_1759_ = lean_usize_shift_right(v_x_1747_, v___x_1758_);
v_x_1746_ = v_node_1757_;
v_x_1747_ = v___x_1759_;
goto _start;
}
default: 
{
uint8_t v___x_1761_; 
v___x_1761_ = 0;
return v___x_1761_;
}
}
}
else
{
lean_object* v_ks_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_ks_1762_ = lean_ctor_get(v_x_1746_, 0);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_1762_, v___x_1763_, v_x_1748_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
size_t v_x_3503__boxed_1768_; uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_x_3503__boxed_1768_ = lean_unbox_usize(v_x_1766_);
lean_dec(v_x_1766_);
v_res_1769_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1765_, v_x_3503__boxed_1768_, v_x_1767_);
lean_dec(v_x_1767_);
lean_dec_ref(v_x_1765_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(lean_object* v_x_1771_, lean_object* v_x_1772_){
_start:
{
uint64_t v___x_1773_; size_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1773_ = l_Lean_instHashableMVarId_hash(v_x_1772_);
v___x_1774_ = lean_uint64_to_usize(v___x_1773_);
v___x_1775_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1771_, v___x_1774_, v_x_1772_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_1776_, lean_object* v_x_1777_){
_start:
{
uint8_t v_res_1778_; lean_object* v_r_1779_; 
v_res_1778_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1776_, v_x_1777_);
lean_dec(v_x_1777_);
lean_dec_ref(v_x_1776_);
v_r_1779_ = lean_box(v_res_1778_);
return v_r_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(lean_object* v_mvarId_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v_mctx_1784_; lean_object* v_eAssignment_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1783_ = lean_st_ref_get(v___y_1781_);
v_mctx_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc_ref(v_mctx_1784_);
lean_dec(v___x_1783_);
v_eAssignment_1785_ = lean_ctor_get(v_mctx_1784_, 8);
lean_inc_ref(v_eAssignment_1785_);
lean_dec_ref(v_mctx_1784_);
v___x_1786_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_eAssignment_1785_, v_mvarId_1780_);
lean_dec_ref(v_eAssignment_1785_);
v___x_1787_ = lean_box(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg___boxed(lean_object* v_mvarId_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec(v_mvarId_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_ref_1799_; lean_object* v___x_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1809_; 
v_ref_1799_ = lean_ctor_get(v___y_1796_, 2);
v___x_1800_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvCheck_spec__0_spec__0_spec__1_spec__2(v_msg_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
lean_inc(v_ref_1799_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_ref_1799_);
lean_ctor_set(v___x_1805_, 1, v_a_1801_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 0, v___x_1805_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg___boxed(lean_object* v_msg_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__1));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(lean_object* v_x_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
lean_inc(v_x_1822_);
v___x_1833_ = l_Lean_Syntax_isOfKind(v_x_1822_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec(v_x_1822_);
v___x_1834_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; lean_object* v_cfg_1836_; lean_object* v_types_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1835_ = lean_unsigned_to_nat(1u);
v_cfg_1836_ = l_Lean_Syntax_getArg(v_x_1822_, v___x_1835_);
v___x_1912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_1836_);
v___x_1913_ = l_Lean_Syntax_isOfKind(v_cfg_1836_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec(v_cfg_1836_);
lean_dec(v_x_1822_);
v___x_1914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1914_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = lean_unsigned_to_nat(2u);
v___x_1916_ = l_Lean_Syntax_getArg(v_x_1822_, v___x_1915_);
lean_dec(v_x_1822_);
v___x_1917_ = l_Lean_Syntax_isNone(v___x_1916_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
lean_inc(v___x_1916_);
v___x_1918_ = l_Lean_Syntax_matchesNull(v___x_1916_, v___x_1835_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
lean_dec(v___x_1916_);
lean_dec(v_cfg_1836_);
v___x_1919_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v_types_1921_; 
v___x_1920_ = lean_unsigned_to_nat(0u);
v_types_1921_ = l_Lean_Syntax_getArg(v___x_1916_, v___x_1920_);
lean_dec(v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__11));
lean_inc(v_types_1921_);
v___x_1925_ = l_Lean_Syntax_isOfKind(v_types_1921_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
lean_dec(v_types_1921_);
lean_dec(v_cfg_1836_);
v___x_1926_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_1926_;
}
else
{
goto v___jp_1922_;
}
}
else
{
goto v___jp_1922_;
}
v___jp_1922_:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_types_1921_);
v_types_1838_ = v___x_1923_;
v___y_1839_ = v_a_1823_;
v___y_1840_ = v_a_1824_;
v___y_1841_ = v_a_1825_;
v___y_1842_ = v_a_1826_;
v___y_1843_ = v_a_1827_;
v___y_1844_ = v_a_1828_;
v___y_1845_ = v_a_1829_;
v___y_1846_ = v_a_1830_;
goto v___jp_1837_;
}
}
}
else
{
lean_object* v___x_1927_; 
lean_dec(v___x_1916_);
v___x_1927_ = lean_box(0);
v_types_1838_ = v___x_1927_;
v___y_1839_ = v_a_1823_;
v___y_1840_ = v_a_1824_;
v___y_1841_ = v_a_1825_;
v___y_1842_ = v_a_1826_;
v___y_1843_ = v_a_1827_;
v___y_1844_ = v_a_1828_;
v___y_1845_ = v_a_1829_;
v___y_1846_ = v_a_1830_;
goto v___jp_1837_;
}
}
v___jp_1837_:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1910_; 
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v___x_1847_, 0);
lean_dec(v_unused_1911_);
v___x_1849_ = v___x_1847_;
v_isShared_1850_ = v_isSharedCheck_1910_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v___x_1847_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1910_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_1840_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v_mvarId_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v_mvarId_1853_ = lean_ctor_get(v_a_1852_, 1);
v___x_1854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__0));
lean_inc(v_mvarId_1853_);
v___x_1855_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_1836_, v_mvarId_1853_, v___x_1854_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideTypes(v_types_1838_, v_a_1856_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_a_1858_);
v___x_1860_ = v___x_1849_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1858_);
v___x_1860_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_1860_, v_a_1856_, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_a_1852_);
v___f_1864_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___boxed), 13, 3);
lean_closure_set(v___f_1864_, 0, v___x_1863_);
lean_closure_set(v___f_1864_, 1, v___x_1861_);
lean_closure_set(v___f_1864_, 2, v___x_1862_);
v___x_1865_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_1864_, v___y_1839_, v___y_1840_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v_snd_1867_; lean_object* v_target_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v_a_1871_; uint8_t v___x_1872_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v_snd_1867_ = lean_ctor_get(v_a_1866_, 1);
lean_inc(v_snd_1867_);
lean_dec(v_a_1866_);
v_target_1868_ = lean_ctor_get(v_snd_1867_, 2);
lean_inc_ref(v_target_1868_);
lean_dec(v_snd_1867_);
v___x_1869_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1868_);
lean_dec_ref(v_target_1868_);
v___x_1870_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v___x_1869_, v___y_1844_);
lean_dec(v___x_1869_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = lean_unbox(v_a_1871_);
lean_dec(v_a_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___closed__2);
v___x_1874_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v___x_1873_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_1875_, v___y_1840_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
return v___x_1876_;
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1865_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1865_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1856_);
lean_dec(v_a_1852_);
lean_del_object(v___x_1849_);
v_a_1886_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1857_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1857_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1852_);
lean_del_object(v___x_1849_);
lean_dec(v_types_1838_);
v_a_1894_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1855_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1855_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_del_object(v___x_1849_);
lean_dec(v_types_1838_);
lean_dec(v_cfg_1836_);
v_a_1902_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1851_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1851_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
else
{
lean_dec(v_types_1838_);
lean_dec(v_cfg_1836_);
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed(lean_object* v_x_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize(v_x_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(lean_object* v_mvarId_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___redArg(v_mvarId_1939_, v___y_1945_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0___boxed(lean_object* v_mvarId_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0(v_mvarId_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_mvarId_1950_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(lean_object* v_00_u03b1_1961_, lean_object* v_msg_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___redArg(v_msg_1962_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_msg_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__1(v_00_u03b1_1973_, v_msg_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1984_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(lean_object* v_00_u03b2_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_){
_start:
{
uint8_t v___x_1988_; 
v___x_1988_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___redArg(v_x_1986_, v_x_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_){
_start:
{
uint8_t v_res_1992_; lean_object* v_r_1993_; 
v_res_1992_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0(v_00_u03b2_1989_, v_x_1990_, v_x_1991_);
lean_dec(v_x_1991_);
lean_dec_ref(v_x_1990_);
v_r_1993_ = lean_box(v_res_1992_);
return v_r_1993_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1994_, lean_object* v_x_1995_, size_t v_x_1996_, lean_object* v_x_1997_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___redArg(v_x_1995_, v_x_1996_, v_x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
size_t v_x_3902__boxed_2003_; uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_x_3902__boxed_2003_ = lean_unbox_usize(v_x_2001_);
lean_dec(v_x_2001_);
v_res_2004_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1(v_00_u03b2_1999_, v_x_2000_, v_x_3902__boxed_2003_, v_x_2002_);
lean_dec(v_x_2002_);
lean_dec_ref(v_x_2000_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2006_, lean_object* v_keys_2007_, lean_object* v_vals_2008_, lean_object* v_heq_2009_, lean_object* v_i_2010_, lean_object* v_k_2011_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2007_, v_i_2010_, v_k_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2013_, lean_object* v_keys_2014_, lean_object* v_vals_2015_, lean_object* v_heq_2016_, lean_object* v_i_2017_, lean_object* v_k_2018_){
_start:
{
uint8_t v_res_2019_; lean_object* v_r_2020_; 
v_res_2019_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2013_, v_keys_2014_, v_vals_2015_, v_heq_2016_, v_i_2017_, v_k_2018_);
lean_dec(v_k_2018_);
lean_dec_ref(v_vals_2015_);
lean_dec_ref(v_keys_2014_);
v_r_2020_ = lean_box(v_res_2019_);
return v_r_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1(){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2026_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvTrace___closed__7));
v___x_2028_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___closed__1));
v___x_2029_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___boxed), 10, 0);
v___x_2030_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2026_, v___x_2027_, v___x_2028_, v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1___boxed(lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize__1();
return v_res_2032_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_4094__overap_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___closed__0);
v___x_4094__overap_2047_ = lean_panic_fn_borrowed(v___x_2046_, v_msg_2034_);
lean_inc(v___y_2044_);
lean_inc_ref(v___y_2043_);
lean_inc(v___y_2042_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2036_);
lean_inc(v___y_2035_);
v___x_2048_ = lean_apply_11(v___x_4094__overap_2047_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, lean_box(0));
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0___boxed(lean_object* v_msg_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v_msg_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec(v___y_2050_);
return v_res_2061_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__2));
v___x_2066_ = lean_unsigned_to_nat(46u);
v___x_2067_ = lean_unsigned_to_nat(113u);
v___x_2068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__1));
v___x_2069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__0));
v___x_2070_ = l_mkPanicMessageWithDecl(v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_, v___x_2065_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(lean_object* v_a_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2083_ = lean_st_ref_get(v___y_2072_);
v___x_2084_ = lean_box(1);
v___x_2085_ = lean_box(0);
v___x_2086_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v___x_2084_, v_a_2071_, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2083_);
v___x_2088_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__2);
v___x_2089_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__5);
v___x_2090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVNormalize___lam__0___closed__6));
v___x_2091_ = 0;
v___x_2092_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2092_, 0, v___x_2088_);
lean_ctor_set(v___x_2092_, 1, v___x_2089_);
lean_ctor_set(v___x_2092_, 2, v___x_2087_);
lean_ctor_set(v___x_2092_, 3, v___x_2090_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*4, v___x_2091_);
v___x_2093_ = lean_st_mk_ref(v___x_2092_);
v___x_2094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_2085_, v___x_2086_, v___x_2093_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec_ref(v___x_2086_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2108_; 
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v___x_2094_, 0);
lean_dec(v_unused_2109_);
v___x_2096_ = v___x_2094_;
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
else
{
lean_dec(v___x_2094_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2108_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v_target_2099_; 
v___x_2098_ = lean_st_ref_get(v___x_2093_);
lean_dec(v___x_2093_);
v_target_2099_ = lean_ctor_get(v___x_2098_, 2);
lean_inc_ref(v_target_2099_);
lean_dec(v___x_2098_);
if (lean_obj_tag(v_target_2099_) == 1)
{
lean_object* v_goal_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v_goal_2100_ = lean_ctor_get(v_target_2099_, 0);
lean_inc_ref(v_goal_2100_);
lean_dec_ref_known(v_target_2099_, 1);
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_st_ref_swap(v___y_2072_, v_goal_2100_);
lean_dec(v___x_2102_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2101_);
v___x_2104_ = v___x_2096_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2101_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec_ref(v_target_2099_);
lean_del_object(v___x_2096_);
v___x_2106_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___closed__3);
v___x_2107_ = l_panic___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush_spec__0(v___x_2106_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2107_;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v___x_2093_);
v_a_2110_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2094_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2094_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed(lean_object* v_a_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0(v_a_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(lean_object* v_x_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
lean_inc(v_x_2141_);
v___x_2150_ = l_Lean_Syntax_isOfKind(v_x_2141_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec(v_x_2141_);
v___x_2151_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2151_;
}
else
{
lean_object* v___x_2152_; lean_object* v_cfg_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2152_ = lean_unsigned_to_nat(1u);
v_cfg_2153_ = l_Lean_Syntax_getArg(v_x_2141_, v___x_2152_);
lean_dec(v_x_2141_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide___closed__9));
lean_inc(v_cfg_2153_);
v___x_2155_ = l_Lean_Syntax_isOfKind(v_cfg_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
lean_dec(v_cfg_2153_);
v___x_2156_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBvDecide_spec__0___redArg();
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Elab_Tactic_BVDecide_ensureBvDecide(v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref_known(v___x_2157_, 1);
v___x_2158_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_mvarId_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v_mvarId_2160_ = lean_ctor_get(v_a_2159_, 1);
lean_inc(v_mvarId_2160_);
lean_dec(v_a_2159_);
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__3));
v___x_2162_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_elabBVDecideConfig___redArg(v_cfg_2153_, v_mvarId_2160_, v___x_2161_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___f_2164_; lean_object* v___x_2165_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___f_2164_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2164_, 0, v_a_2163_);
v___x_2165_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___f_2164_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
return v___x_2165_;
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
v_a_2166_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2162_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2162_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_cfg_2153_);
v_a_2174_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2158_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2158_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_dec(v_cfg_2153_);
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___boxed(lean_object* v_x_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(lean_object* v_x_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg(v_x_2191_, v_a_2192_, v_a_2193_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed(lean_object* v_x_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush(v_x_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1(){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2218_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_2219_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___redArg___closed__1));
v___x_2220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___closed__1));
v___x_2221_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___boxed), 10, 0);
v___x_2222_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2218_, v___x_2219_, v___x_2220_, v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1___boxed(lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush___regBuiltin___private_Lean_Elab_Tactic_Grind_BVDecide_0__Lean_Elab_Tactic_Grind_evalBVPush__1();
return v_res_2224_;
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
