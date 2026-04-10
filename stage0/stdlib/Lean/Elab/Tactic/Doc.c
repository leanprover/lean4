// Lean compiler output
// Module: Lean.Elab.Tactic.Doc
// Imports: import Lean.DocString public import Lean.Elab.Command public import Lean.Parser.Tactic.Doc
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tactic_extension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 145, 122, 23, 135, 199, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Malformed tactic extension command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Missing documentation comment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Malformed 'register_tactic_tag' command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_tactic_tag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 57, 11, 65, 76, 175, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 185, 128, 48, 210, 24, 186)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " — \""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0;
static const lean_array_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Available tags: "};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Displays all available tactic tags, with documentation.\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1_, v___x_2_, v___y_7_, v___y_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(v___x_11_, v___x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_20_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_21_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
lean_ctor_set(v___x_26_, 3, v___x_25_);
lean_ctor_set(v___x_26_, 4, v___x_24_);
lean_ctor_set(v___x_26_, 5, v___x_24_);
lean_ctor_set(v___x_26_, 6, v___x_24_);
lean_ctor_set(v___x_26_, 7, v___x_24_);
lean_ctor_set(v___x_26_, 8, v___x_24_);
lean_ctor_set(v___x_26_, 9, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(32u);
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4(void){
_start:
{
size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_30_ = ((size_t)5ULL);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_unsigned_to_nat(32u);
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_34_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3);
v___x_35_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_31_);
lean_ctor_set(v___x_35_, 3, v___x_31_);
lean_ctor_set_usize(v___x_35_, 4, v___x_30_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_box(1);
v___x_37_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_38_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object* v_msgData_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v_env_44_; lean_object* v___x_45_; lean_object* v_scopes_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_opts_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_43_ = lean_st_ref_get(v___y_41_);
v_env_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_env_44_);
lean_dec(v___x_43_);
v___x_45_ = lean_st_ref_get(v___y_41_);
v_scopes_46_ = lean_ctor_get(v___x_45_, 2);
lean_inc(v_scopes_46_);
lean_dec(v___x_45_);
v___x_47_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_48_ = l_List_head_x21___redArg(v___x_47_, v_scopes_46_);
lean_dec(v_scopes_46_);
v_opts_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc_ref(v_opts_49_);
lean_dec(v___x_48_);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5);
v___x_52_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_52_, 0, v_env_44_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v_opts_49_);
v___x_53_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_msgData_40_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_55_, v___y_56_);
lean_dec(v___y_56_);
return v_res_58_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(1);
v___x_60_ = l_Lean_MessageData_ofFormat(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2));
v___x_65_ = l_Lean_MessageData_ofFormat(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
return v_x_66_;
}
else
{
lean_object* v_head_68_; lean_object* v_tail_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_91_; 
v_head_68_ = lean_ctor_get(v_x_67_, 0);
v_tail_69_ = lean_ctor_get(v_x_67_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_71_ = v_x_67_;
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_tail_69_);
lean_inc(v_head_68_);
lean_dec(v_x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_before_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_89_; 
v_before_73_ = lean_ctor_get(v_head_68_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_head_68_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_head_68_, 1);
lean_dec(v_unused_90_);
v___x_75_ = v_head_68_;
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_before_73_);
lean_dec(v_head_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 7);
lean_ctor_set(v___x_75_, 1, v___x_77_);
lean_ctor_set(v___x_75_, 0, v_x_66_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_x_66_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_88_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 7);
lean_ctor_set(v___x_71_, 1, v___x_80_);
lean_ctor_set(v___x_71_, 0, v___x_79_);
v___x_82_ = v___x_71_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_87_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = l_Lean_MessageData_ofSyntax(v_before_73_);
v___x_84_ = l_Lean_indentD(v___x_83_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v_x_66_ = v___x_85_;
v_x_67_ = v_tail_69_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object* v_opts_92_, lean_object* v_opt_93_){
_start:
{
lean_object* v_name_94_; lean_object* v_defValue_95_; lean_object* v_map_96_; lean_object* v___x_97_; 
v_name_94_ = lean_ctor_get(v_opt_93_, 0);
v_defValue_95_ = lean_ctor_get(v_opt_93_, 1);
v_map_96_ = lean_ctor_get(v_opts_92_, 0);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_96_, v_name_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
uint8_t v___x_98_; 
v___x_98_ = lean_unbox(v_defValue_95_);
return v___x_98_;
}
else
{
lean_object* v_val_99_; 
v_val_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_99_);
lean_dec_ref(v___x_97_);
if (lean_obj_tag(v_val_99_) == 1)
{
uint8_t v_v_100_; 
v_v_100_ = lean_ctor_get_uint8(v_val_99_, 0);
lean_dec_ref(v_val_99_);
return v_v_100_;
}
else
{
uint8_t v___x_101_; 
lean_dec(v_val_99_);
v___x_101_ = lean_unbox(v_defValue_95_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_102_, lean_object* v_opt_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_102_, v_opt_103_);
lean_dec_ref(v_opt_103_);
lean_dec_ref(v_opts_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1));
v___x_110_ = l_Lean_MessageData_ofFormat(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object* v_msgData_111_, lean_object* v_macroStack_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_scopes_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_opts_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_115_ = lean_st_ref_get(v___y_113_);
v_scopes_116_ = lean_ctor_get(v___x_115_, 2);
lean_inc(v_scopes_116_);
lean_dec(v___x_115_);
v___x_117_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_118_ = l_List_head_x21___redArg(v___x_117_, v_scopes_116_);
lean_dec(v_scopes_116_);
v_opts_119_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_opts_119_);
lean_dec(v___x_118_);
v___x_120_ = l_Lean_Elab_pp_macroStack;
v___x_121_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_119_, v___x_120_);
lean_dec_ref(v_opts_119_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v_macroStack_112_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v_msgData_111_);
return v___x_122_;
}
else
{
if (lean_obj_tag(v_macroStack_112_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v_msgData_111_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_after_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_140_; 
v_head_124_ = lean_ctor_get(v_macroStack_112_, 0);
lean_inc(v_head_124_);
v_after_125_ = lean_ctor_get(v_head_124_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_head_124_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_head_124_, 0);
lean_dec(v_unused_141_);
v___x_127_ = v_head_124_;
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_after_125_);
lean_dec(v_head_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 7);
lean_ctor_set(v___x_127_, 1, v___x_129_);
lean_ctor_set(v___x_127_, 0, v_msgData_111_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_msgData_111_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_139_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_msgData_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2);
v___x_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = l_Lean_MessageData_ofSyntax(v_after_125_);
v___x_135_ = l_Lean_indentD(v___x_134_);
v_msgData_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_136_, 0, v___x_133_);
lean_ctor_set(v_msgData_136_, 1, v___x_135_);
v___x_137_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(v_msgData_136_, v_macroStack_112_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_142_, lean_object* v_macroStack_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_142_, v_macroStack_143_, v___y_144_);
lean_dec(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_Command_getRef___redArg(v___y_148_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v_macroStack_153_; lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref(v___x_151_);
v_macroStack_153_ = lean_ctor_get(v___y_148_, 4);
v___x_154_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_147_, v___y_149_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
lean_inc_n(v_macroStack_153_, 2);
v___x_156_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
v___x_157_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_a_155_, v_macroStack_153_, v___y_149_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_156_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v_msg_147_);
v_a_167_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_151_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_151_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object* v_ref_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_Command_getRef___redArg(v___y_182_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_currRecDepth_189_; lean_object* v_cmdPos_190_; lean_object* v_macroStack_191_; lean_object* v_quotContext_x3f_192_; lean_object* v_currMacroScope_193_; lean_object* v_snap_x3f_194_; lean_object* v_cancelTk_x3f_195_; uint8_t v_suppressElabErrors_196_; lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref(v___x_185_);
v_fileName_187_ = lean_ctor_get(v___y_182_, 0);
v_fileMap_188_ = lean_ctor_get(v___y_182_, 1);
v_currRecDepth_189_ = lean_ctor_get(v___y_182_, 2);
v_cmdPos_190_ = lean_ctor_get(v___y_182_, 3);
v_macroStack_191_ = lean_ctor_get(v___y_182_, 4);
v_quotContext_x3f_192_ = lean_ctor_get(v___y_182_, 5);
v_currMacroScope_193_ = lean_ctor_get(v___y_182_, 6);
v_snap_x3f_194_ = lean_ctor_get(v___y_182_, 8);
v_cancelTk_x3f_195_ = lean_ctor_get(v___y_182_, 9);
v_suppressElabErrors_196_ = lean_ctor_get_uint8(v___y_182_, sizeof(void*)*10);
v_ref_197_ = l_Lean_replaceRef(v_ref_180_, v_a_186_);
lean_dec(v_a_186_);
lean_inc(v_cancelTk_x3f_195_);
lean_inc(v_snap_x3f_194_);
lean_inc(v_currMacroScope_193_);
lean_inc(v_quotContext_x3f_192_);
lean_inc(v_macroStack_191_);
lean_inc(v_cmdPos_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___x_198_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_198_, 0, v_fileName_187_);
lean_ctor_set(v___x_198_, 1, v_fileMap_188_);
lean_ctor_set(v___x_198_, 2, v_currRecDepth_189_);
lean_ctor_set(v___x_198_, 3, v_cmdPos_190_);
lean_ctor_set(v___x_198_, 4, v_macroStack_191_);
lean_ctor_set(v___x_198_, 5, v_quotContext_x3f_192_);
lean_ctor_set(v___x_198_, 6, v_currMacroScope_193_);
lean_ctor_set(v___x_198_, 7, v_ref_197_);
lean_ctor_set(v___x_198_, 8, v_snap_x3f_194_);
lean_ctor_set(v___x_198_, 9, v_cancelTk_x3f_195_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*10, v_suppressElabErrors_196_);
v___x_199_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_181_, v___x_198_, v___y_183_);
lean_dec_ref(v___x_198_);
return v___x_199_;
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_msg_181_);
v_a_200_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_185_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_185_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object* v_ref_208_, lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_208_, v_msg_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v_ref_208_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
lean_inc(v_x_247_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_247_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_x_247_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_254_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_253_, v_a_248_, v_a_249_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_Lean_Syntax_getArg(v_x_247_, v___x_255_);
lean_inc(v___x_256_);
v___x_257_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_256_);
v___x_259_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v___x_256_);
lean_dec(v_x_247_);
v___x_260_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_260_, v_a_248_, v_a_249_);
return v___x_261_;
}
else
{
lean_object* v_docs_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_docs_262_ = l_Lean_Syntax_getArg(v___x_256_, v___x_255_);
lean_dec(v___x_256_);
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_docs_262_);
v___x_264_ = l_Lean_Syntax_isOfKind(v_docs_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_docs_262_);
lean_dec(v_x_247_);
v___x_265_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_266_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_265_, v_a_248_, v_a_249_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_267_ = lean_unsigned_to_nat(2u);
v___x_268_ = l_Lean_Syntax_getArg(v_x_247_, v___x_267_);
lean_dec(v_x_247_);
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v___x_268_);
v___x_270_ = l_Lean_Syntax_isOfKind(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v___x_271_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_271_, v_a_248_, v_a_249_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
lean_inc(v___x_268_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_274_, 0, v___x_268_);
lean_closure_set(v___f_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_274_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_342_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_342_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_342_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_342_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___y_281_; lean_object* v___y_314_; lean_object* v___y_315_; uint8_t v___y_316_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v___x_331_; 
v___x_329_ = lean_st_ref_get(v_a_249_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
lean_inc(v_a_276_);
v___x_331_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_330_, v_a_276_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_334_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_MessageData_ofConstName(v_val_332_, v___x_257_);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_333_);
v___x_341_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_340_, v_a_248_, v_a_249_);
lean_dec(v___x_268_);
return v___x_341_;
}
else
{
lean_dec(v___x_331_);
v___y_324_ = v_a_248_;
v___y_325_ = v_a_249_;
goto v___jp_323_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v_messages_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_312_; 
v___x_282_ = lean_st_ref_take(v___y_281_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
v_messages_284_ = lean_ctor_get(v___x_282_, 1);
v_scopes_285_ = lean_ctor_get(v___x_282_, 2);
v_usedQuotCtxts_286_ = lean_ctor_get(v___x_282_, 3);
v_nextMacroScope_287_ = lean_ctor_get(v___x_282_, 4);
v_maxRecDepth_288_ = lean_ctor_get(v___x_282_, 5);
v_ngen_289_ = lean_ctor_get(v___x_282_, 6);
v_auxDeclNGen_290_ = lean_ctor_get(v___x_282_, 7);
v_infoState_291_ = lean_ctor_get(v___x_282_, 8);
v_traceState_292_ = lean_ctor_get(v___x_282_, 9);
v_snapshotTasks_293_ = lean_ctor_get(v___x_282_, 10);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_312_ == 0)
{
v___x_295_ = v___x_282_;
v_isShared_296_ = v_isSharedCheck_312_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_snapshotTasks_293_);
lean_inc(v_traceState_292_);
lean_inc(v_infoState_291_);
lean_inc(v_auxDeclNGen_290_);
lean_inc(v_ngen_289_);
lean_inc(v_maxRecDepth_288_);
lean_inc(v_nextMacroScope_287_);
lean_inc(v_usedQuotCtxts_286_);
lean_inc(v_scopes_285_);
lean_inc(v_messages_284_);
lean_inc(v_env_283_);
lean_dec(v___x_282_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_312_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v_toEnvExtension_298_; lean_object* v_asyncMode_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_297_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_298_ = lean_ctor_get(v___x_297_, 0);
v_asyncMode_299_ = lean_ctor_get(v_toEnvExtension_298_, 2);
v___x_300_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_a_276_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_297_, v_env_283_, v___x_301_, v_asyncMode_299_, v___x_302_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_303_);
v___x_305_ = v___x_295_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_messages_284_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_311_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_311_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_311_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_311_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_311_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_311_, 10, v_snapshotTasks_293_);
v___x_305_ = v_reuseFailAlloc_311_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = lean_st_ref_set(v___y_281_, v___x_305_);
v___x_307_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_307_);
v___x_309_ = v___x_278_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
v___jp_313_:
{
if (v___y_316_ == 0)
{
lean_dec(v___x_268_);
v___y_281_ = v___y_315_;
goto v___jp_280_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v___x_317_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_318_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_321_, v___y_314_, v___y_315_);
lean_dec(v___x_268_);
return v___x_322_;
}
}
v___jp_323_:
{
lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; 
v___x_326_ = lean_st_ref_get(v___y_325_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_327_, v_a_276_);
if (v___x_328_ == 0)
{
v___y_314_ = v___y_324_;
v___y_315_ = v___y_325_;
v___y_316_ = v___x_270_;
goto v___jp_313_;
}
else
{
v___y_314_ = v___y_324_;
v___y_315_ = v___y_325_;
v___y_316_ = v___x_257_;
goto v___jp_313_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v_a_343_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_275_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_275_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v_cmd_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v___x_256_);
v___x_351_ = lean_unsigned_to_nat(1u);
v_cmd_352_ = l_Lean_Syntax_getArg(v_x_247_, v___x_351_);
lean_dec(v_x_247_);
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_354_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_352_, v___x_353_, v_a_248_, v_a_249_);
lean_dec(v_cmd_352_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_360_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_376_, v_msg_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_ref_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_383_, v_msg_384_, v___y_385_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_389_, lean_object* v_ref_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_389_, v_ref_390_, v_msg_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_ref_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_396_, lean_object* v_macroStack_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_396_, v_macroStack_397_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_402_, lean_object* v_macroStack_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_402_, v_macroStack_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_419_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_422_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_423_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_419_, v___x_420_, v___x_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_454_ = l_Lean_addBuiltinDeclarationRanges(v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_456_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_val_472_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_479_);
switch(lean_obj_tag(v___x_480_))
{
case 2:
{
lean_object* v_val_481_; 
lean_dec(v_stx_461_);
v_val_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc_ref(v_val_481_);
lean_dec_ref(v___x_480_);
v_val_472_ = v_val_481_;
goto v___jp_471_;
}
case 1:
{
lean_object* v_kind_482_; 
v_kind_482_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_kind_482_);
if (lean_obj_tag(v_kind_482_) == 1)
{
lean_object* v_pre_483_; 
v_pre_483_ = lean_ctor_get(v_kind_482_, 0);
lean_inc(v_pre_483_);
if (lean_obj_tag(v_pre_483_) == 1)
{
lean_object* v_pre_484_; 
v_pre_484_ = lean_ctor_get(v_pre_483_, 0);
lean_inc(v_pre_484_);
if (lean_obj_tag(v_pre_484_) == 1)
{
lean_object* v_pre_485_; 
v_pre_485_ = lean_ctor_get(v_pre_484_, 0);
lean_inc(v_pre_485_);
if (lean_obj_tag(v_pre_485_) == 1)
{
lean_object* v_pre_486_; 
v_pre_486_ = lean_ctor_get(v_pre_485_, 0);
if (lean_obj_tag(v_pre_486_) == 0)
{
lean_object* v_str_487_; lean_object* v_str_488_; lean_object* v_str_489_; lean_object* v_str_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_str_487_ = lean_ctor_get(v_kind_482_, 1);
lean_inc_ref(v_str_487_);
lean_dec_ref(v_kind_482_);
v_str_488_ = lean_ctor_get(v_pre_483_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref(v_pre_483_);
v_str_489_ = lean_ctor_get(v_pre_484_, 1);
lean_inc_ref(v_str_489_);
lean_dec_ref(v_pre_484_);
v_str_490_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref(v_pre_485_);
v___x_491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_492_ = lean_string_dec_eq(v_str_490_, v___x_491_);
lean_dec_ref(v_str_490_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
else
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_494_ = lean_string_dec_eq(v_str_489_, v___x_493_);
lean_dec_ref(v_str_489_);
if (v___x_494_ == 0)
{
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
else
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_496_ = lean_string_dec_eq(v_str_488_, v___x_495_);
lean_dec_ref(v_str_488_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_str_487_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
else
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_498_ = lean_string_dec_eq(v_str_487_, v___x_497_);
lean_dec_ref(v_str_487_);
if (v___x_498_ == 0)
{
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Lean_Syntax_getArg(v___x_480_, v___x_499_);
lean_dec_ref(v___x_480_);
if (lean_obj_tag(v___x_500_) == 2)
{
lean_object* v_val_501_; 
lean_dec(v_stx_461_);
v_val_501_ = lean_ctor_get(v___x_500_, 1);
lean_inc_ref(v_val_501_);
lean_dec_ref(v___x_500_);
v_val_472_ = v_val_501_;
goto v___jp_471_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v___x_500_);
v___x_502_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_461_);
v___x_503_ = l_Lean_MessageData_ofSyntax(v_stx_461_);
v___x_504_ = l_Lean_indentD(v___x_503_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_502_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_461_, v___x_505_, v___y_462_, v___y_463_);
lean_dec(v_stx_461_);
return v___x_506_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_485_);
lean_dec_ref(v_pre_484_);
lean_dec_ref(v_pre_483_);
lean_dec_ref(v_kind_482_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v_pre_484_);
lean_dec(v_pre_485_);
lean_dec_ref(v_pre_483_);
lean_dec_ref(v_kind_482_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v_pre_483_);
lean_dec(v_pre_484_);
lean_dec_ref(v_kind_482_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec(v_pre_483_);
lean_dec_ref(v_kind_482_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v___x_480_);
lean_dec(v_kind_482_);
goto v___jp_465_;
}
}
default: 
{
lean_dec(v___x_480_);
goto v___jp_465_;
}
}
v___jp_465_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_461_);
v___x_467_ = l_Lean_MessageData_ofSyntax(v_stx_461_);
v___x_468_ = l_Lean_indentD(v___x_467_);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_466_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_461_, v___x_469_, v___y_462_, v___y_463_);
lean_dec(v_stx_461_);
return v___x_470_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_string_utf8_byte_size(v_val_472_);
v___x_475_ = lean_unsigned_to_nat(2u);
v___x_476_ = lean_nat_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_string_utf8_extract(v_val_472_, v___x_473_, v___x_476_);
lean_dec(v___x_476_);
lean_dec_ref(v_val_472_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v_a_532_; lean_object* v_doc_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_524_);
v___x_600_ = l_Lean_Syntax_isOfKind(v_x_524_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_x_524_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_601_, v_a_525_, v_a_526_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = l_Lean_Syntax_getArg(v_x_524_, v___x_603_);
v___x_605_ = l_Lean_Syntax_isNone(v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_604_);
v___x_607_ = l_Lean_Syntax_matchesNull(v___x_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___x_604_);
lean_dec(v_x_524_);
v___x_608_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_609_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_608_, v_a_525_, v_a_526_);
return v___x_609_;
}
else
{
lean_object* v_doc_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_doc_610_ = l_Lean_Syntax_getArg(v___x_604_, v___x_603_);
lean_dec(v___x_604_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_doc_610_);
v___x_612_ = l_Lean_Syntax_isOfKind(v_doc_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_doc_610_);
lean_dec(v_x_524_);
v___x_613_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_614_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_613_, v_a_525_, v_a_526_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v_doc_610_);
v_doc_565_ = v___x_615_;
v___y_566_ = v_a_525_;
v___y_567_ = v_a_526_;
goto v___jp_564_;
}
}
}
else
{
lean_object* v___x_616_; 
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_doc_565_ = v___x_616_;
v___y_566_ = v_a_525_;
v___y_567_ = v_a_526_;
goto v___jp_564_;
}
}
v___jp_528_:
{
lean_object* v___x_533_; lean_object* v_env_534_; lean_object* v_messages_535_; lean_object* v_scopes_536_; lean_object* v_usedQuotCtxts_537_; lean_object* v_nextMacroScope_538_; lean_object* v_maxRecDepth_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_infoState_542_; lean_object* v_traceState_543_; lean_object* v_snapshotTasks_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_563_; 
v___x_533_ = lean_st_ref_take(v___y_529_);
v_env_534_ = lean_ctor_get(v___x_533_, 0);
v_messages_535_ = lean_ctor_get(v___x_533_, 1);
v_scopes_536_ = lean_ctor_get(v___x_533_, 2);
v_usedQuotCtxts_537_ = lean_ctor_get(v___x_533_, 3);
v_nextMacroScope_538_ = lean_ctor_get(v___x_533_, 4);
v_maxRecDepth_539_ = lean_ctor_get(v___x_533_, 5);
v_ngen_540_ = lean_ctor_get(v___x_533_, 6);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_533_, 7);
v_infoState_542_ = lean_ctor_get(v___x_533_, 8);
v_traceState_543_ = lean_ctor_get(v___x_533_, 9);
v_snapshotTasks_544_ = lean_ctor_get(v___x_533_, 10);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_563_ == 0)
{
v___x_546_ = v___x_533_;
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snapshotTasks_544_);
lean_inc(v_traceState_543_);
lean_inc(v_infoState_542_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_maxRecDepth_539_);
lean_inc(v_nextMacroScope_538_);
lean_inc(v_usedQuotCtxts_537_);
lean_inc(v_scopes_536_);
lean_inc(v_messages_535_);
lean_inc(v_env_534_);
lean_dec(v___x_533_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v_toEnvExtension_549_; lean_object* v_asyncMode_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_548_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_549_ = lean_ctor_get(v___x_548_, 0);
v_asyncMode_550_ = lean_ctor_get(v_toEnvExtension_549_, 2);
v___x_551_ = l_Lean_TSyntax_getId(v___y_531_);
lean_dec(v___y_531_);
v___x_552_ = l_Lean_TSyntax_getString(v___y_530_);
lean_dec(v___y_530_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_532_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_box(0);
v___x_556_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_548_, v_env_534_, v___x_554_, v_asyncMode_550_, v___x_555_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_556_);
v___x_558_ = v___x_546_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_messages_535_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_scopes_536_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_usedQuotCtxts_537_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_nextMacroScope_538_);
lean_ctor_set(v_reuseFailAlloc_562_, 5, v_maxRecDepth_539_);
lean_ctor_set(v_reuseFailAlloc_562_, 6, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 7, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_562_, 8, v_infoState_542_);
lean_ctor_set(v_reuseFailAlloc_562_, 9, v_traceState_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 10, v_snapshotTasks_544_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_st_ref_set(v___y_529_, v___x_558_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
v___jp_564_:
{
lean_object* v___x_568_; lean_object* v_tag_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_568_ = lean_unsigned_to_nat(2u);
v_tag_569_ = l_Lean_Syntax_getArg(v_x_524_, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v_tag_569_);
v___x_571_ = l_Lean_Syntax_isOfKind(v_tag_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_tag_569_);
lean_dec(v_doc_565_);
lean_dec(v_x_524_);
v___x_572_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_573_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_572_, v___y_566_, v___y_567_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v_user_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_574_ = lean_unsigned_to_nat(3u);
v_user_575_ = l_Lean_Syntax_getArg(v_x_524_, v___x_574_);
lean_dec(v_x_524_);
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_575_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_user_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_user_575_);
lean_dec(v_tag_569_);
lean_dec(v_doc_565_);
v___x_578_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_579_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_578_, v___y_566_, v___y_567_);
return v___x_579_;
}
else
{
if (lean_obj_tag(v_doc_565_) == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
v___y_529_ = v___y_567_;
v___y_530_ = v_user_575_;
v___y_531_ = v_tag_569_;
v_a_532_ = v___x_580_;
goto v___jp_528_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_598_; 
v_val_581_ = lean_ctor_get(v_doc_565_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_doc_565_);
if (v_isSharedCheck_598_ == 0)
{
v___x_583_ = v_doc_565_;
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v_doc_565_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_581_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref(v___x_585_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_a_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v___y_529_ = v___y_567_;
v___y_530_ = v_user_575_;
v___y_531_ = v_tag_569_;
v_a_532_ = v___x_588_;
goto v___jp_528_;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_del_object(v___x_583_);
lean_dec(v_user_575_);
lean_dec(v_tag_569_);
v_a_590_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_585_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_585_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_631_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_634_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_630_, v___x_631_, v___x_632_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_665_ = l_Lean_addBuiltinDeclarationRanges(v___x_663_, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
return v___x_670_;
}
else
{
lean_dec_ref(v___x_668_);
lean_inc_ref(v_x_669_);
return v_x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_671_, v_x_672_);
lean_dec(v_x_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_674_, lean_object* v_k_675_, lean_object* v_t_676_){
_start:
{
if (lean_obj_tag(v_t_676_) == 0)
{
lean_object* v_size_677_; lean_object* v_k_678_; lean_object* v_v_679_; lean_object* v_l_680_; lean_object* v_r_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_1007_; 
v_size_677_ = lean_ctor_get(v_t_676_, 0);
v_k_678_ = lean_ctor_get(v_t_676_, 1);
v_v_679_ = lean_ctor_get(v_t_676_, 2);
v_l_680_ = lean_ctor_get(v_t_676_, 3);
v_r_681_ = lean_ctor_get(v_t_676_, 4);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_t_676_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_683_ = v_t_676_;
v_isShared_684_ = v_isSharedCheck_1007_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_r_681_);
lean_inc(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
lean_inc(v_size_677_);
lean_dec(v_t_676_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_1007_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; 
v___x_685_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_675_, v_k_678_);
switch(v___x_685_)
{
case 0:
{
lean_object* v_impl_686_; lean_object* v___x_687_; 
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
v_impl_686_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_674_, v_k_675_, v_l_680_);
v___x_687_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_678_, v_v_679_, v_impl_686_, v_r_681_);
return v___x_687_;
}
case 1:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_k_678_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_v_679_);
v___x_689_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_674_, v___x_688_);
lean_dec_ref(v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
lean_dec(v_k_675_);
if (lean_obj_tag(v_l_680_) == 0)
{
if (lean_obj_tag(v_r_681_) == 0)
{
lean_object* v_size_690_; lean_object* v_k_691_; lean_object* v_v_692_; lean_object* v_l_693_; lean_object* v_r_694_; lean_object* v_size_695_; lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_l_698_; lean_object* v_r_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_size_690_ = lean_ctor_get(v_l_680_, 0);
v_k_691_ = lean_ctor_get(v_l_680_, 1);
v_v_692_ = lean_ctor_get(v_l_680_, 2);
v_l_693_ = lean_ctor_get(v_l_680_, 3);
v_r_694_ = lean_ctor_get(v_l_680_, 4);
lean_inc(v_r_694_);
v_size_695_ = lean_ctor_get(v_r_681_, 0);
v_k_696_ = lean_ctor_get(v_r_681_, 1);
v_v_697_ = lean_ctor_get(v_r_681_, 2);
v_l_698_ = lean_ctor_get(v_r_681_, 3);
lean_inc(v_l_698_);
v_r_699_ = lean_ctor_get(v_r_681_, 4);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_dec_lt(v_size_690_, v_size_695_);
if (v___x_701_ == 0)
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_837_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
v_isSharedCheck_837_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_838_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_842_);
v___x_703_ = v_l_680_;
v_isShared_704_ = v_isSharedCheck_837_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_l_680_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_837_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v_tree_706_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_691_, v_v_692_, v_l_693_, v_r_694_);
v_tree_706_ = lean_ctor_get(v___x_705_, 2);
lean_inc(v_tree_706_);
if (lean_obj_tag(v_tree_706_) == 0)
{
lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v_size_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_k_707_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_707_);
v_v_708_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_708_);
lean_dec_ref(v___x_705_);
v_size_709_ = lean_ctor_get(v_tree_706_, 0);
v___x_710_ = lean_unsigned_to_nat(3u);
v___x_711_ = lean_nat_mul(v___x_710_, v_size_709_);
v___x_712_ = lean_nat_dec_lt(v___x_711_, v_size_695_);
lean_dec(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_l_698_);
v___x_713_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_714_ = lean_nat_add(v___x_713_, v_size_695_);
lean_dec(v___x_713_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_681_);
lean_ctor_set(v___x_703_, 3, v_tree_706_);
lean_ctor_set(v___x_703_, 2, v_v_708_);
lean_ctor_set(v___x_703_, 1, v_k_707_);
lean_ctor_set(v___x_703_, 0, v___x_714_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_r_681_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_772_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_772_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_773_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_777_);
v___x_719_ = v_r_681_;
v_isShared_720_ = v_isSharedCheck_772_;
goto v_resetjp_718_;
}
else
{
lean_dec(v_r_681_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_772_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_size_721_; lean_object* v_k_722_; lean_object* v_v_723_; lean_object* v_l_724_; lean_object* v_r_725_; lean_object* v_size_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_size_721_ = lean_ctor_get(v_l_698_, 0);
v_k_722_ = lean_ctor_get(v_l_698_, 1);
v_v_723_ = lean_ctor_get(v_l_698_, 2);
v_l_724_ = lean_ctor_get(v_l_698_, 3);
v_r_725_ = lean_ctor_get(v_l_698_, 4);
v_size_726_ = lean_ctor_get(v_r_699_, 0);
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = lean_nat_mul(v___x_727_, v_size_726_);
v___x_729_ = lean_nat_dec_lt(v_size_721_, v___x_728_);
lean_dec(v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_757_; 
lean_inc(v_r_725_);
lean_inc(v_l_724_);
lean_inc(v_v_723_);
lean_inc(v_k_722_);
v_isSharedCheck_757_ = !lean_is_exclusive(v_l_698_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; 
v_unused_758_ = lean_ctor_get(v_l_698_, 4);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_698_, 3);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_l_698_, 2);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_l_698_, 1);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_l_698_, 0);
lean_dec(v_unused_762_);
v___x_731_ = v_l_698_;
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
else
{
lean_dec(v_l_698_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_747_; 
v___x_733_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_734_ = lean_nat_add(v___x_733_, v_size_695_);
lean_dec(v_size_695_);
if (lean_obj_tag(v_l_724_) == 0)
{
lean_object* v_size_755_; 
v_size_755_ = lean_ctor_get(v_l_724_, 0);
lean_inc(v_size_755_);
v___y_747_ = v_size_755_;
goto v___jp_746_;
}
else
{
lean_object* v___x_756_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___y_747_ = v___x_756_;
goto v___jp_746_;
}
v___jp_735_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_nat_add(v___y_736_, v___y_738_);
lean_dec(v___y_738_);
lean_dec(v___y_736_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 4, v_r_699_);
lean_ctor_set(v___x_731_, 3, v_r_725_);
lean_ctor_set(v___x_731_, 2, v_v_697_);
lean_ctor_set(v___x_731_, 1, v_k_696_);
lean_ctor_set(v___x_731_, 0, v___x_739_);
v___x_741_ = v___x_731_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_r_725_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_r_699_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v___x_741_);
lean_ctor_set(v___x_719_, 3, v___y_737_);
lean_ctor_set(v___x_719_, 2, v_v_723_);
lean_ctor_set(v___x_719_, 1, v_k_722_);
lean_ctor_set(v___x_719_, 0, v___x_734_);
v___x_743_ = v___x_719_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_722_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_723_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v___y_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_nat_add(v___x_733_, v___y_747_);
lean_dec(v___y_747_);
lean_dec(v___x_733_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_l_724_);
lean_ctor_set(v___x_703_, 3, v_tree_706_);
lean_ctor_set(v___x_703_, 2, v_v_708_);
lean_ctor_set(v___x_703_, 1, v_k_707_);
lean_ctor_set(v___x_703_, 0, v___x_748_);
v___x_750_ = v___x_703_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_l_724_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; 
v___x_751_ = lean_nat_add(v___x_700_, v_size_726_);
if (lean_obj_tag(v_r_725_) == 0)
{
lean_object* v_size_752_; 
v_size_752_ = lean_ctor_get(v_r_725_, 0);
lean_inc(v_size_752_);
v___y_736_ = v___x_751_;
v___y_737_ = v___x_750_;
v___y_738_ = v_size_752_;
goto v___jp_735_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___y_736_ = v___x_751_;
v___y_737_ = v___x_750_;
v___y_738_ = v___x_753_;
goto v___jp_735_;
}
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_763_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_764_ = lean_nat_add(v___x_763_, v_size_695_);
lean_dec(v_size_695_);
v___x_765_ = lean_nat_add(v___x_763_, v_size_721_);
lean_dec(v___x_763_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v_l_698_);
lean_ctor_set(v___x_719_, 3, v_tree_706_);
lean_ctor_set(v___x_719_, 2, v_v_708_);
lean_ctor_set(v___x_719_, 1, v_k_707_);
lean_ctor_set(v___x_719_, 0, v___x_765_);
v___x_767_ = v___x_719_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_l_698_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_767_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_764_);
v___x_769_ = v___x_703_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_r_699_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
else
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_831_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_832_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_836_);
v___x_779_ = v_r_681_;
v_isShared_780_ = v_isSharedCheck_831_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_r_681_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_831_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
if (lean_obj_tag(v_l_698_) == 0)
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_781_; lean_object* v_v_782_; lean_object* v_size_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v_k_781_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_781_);
v_v_782_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_782_);
lean_dec_ref(v___x_705_);
v_size_783_ = lean_ctor_get(v_l_698_, 0);
v___x_784_ = lean_nat_add(v___x_700_, v_size_695_);
lean_dec(v_size_695_);
v___x_785_ = lean_nat_add(v___x_700_, v_size_783_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_698_);
lean_ctor_set(v___x_779_, 3, v_tree_706_);
lean_ctor_set(v___x_779_, 2, v_v_782_);
lean_ctor_set(v___x_779_, 1, v_k_781_);
lean_ctor_set(v___x_779_, 0, v___x_785_);
v___x_787_ = v___x_779_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_l_698_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_787_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_784_);
v___x_789_ = v___x_703_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_r_699_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_size_695_);
v_k_792_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_792_);
v_v_793_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_793_);
lean_dec_ref(v___x_705_);
v_k_794_ = lean_ctor_get(v_l_698_, 1);
v_v_795_ = lean_ctor_get(v_l_698_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_l_698_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_810_ = lean_ctor_get(v_l_698_, 4);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_l_698_, 3);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_l_698_, 0);
lean_dec(v_unused_812_);
v___x_797_ = v_l_698_;
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_v_795_);
lean_inc(v_k_794_);
lean_dec(v_l_698_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_unsigned_to_nat(3u);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 4, v_r_699_);
lean_ctor_set(v___x_797_, 3, v_r_699_);
lean_ctor_set(v___x_797_, 2, v_v_793_);
lean_ctor_set(v___x_797_, 1, v_k_792_);
lean_ctor_set(v___x_797_, 0, v___x_700_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_r_699_);
v___x_801_ = v_reuseFailAlloc_808_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 3, v_r_699_);
lean_ctor_set(v___x_779_, 0, v___x_700_);
v___x_803_ = v___x_779_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_r_699_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_803_);
lean_ctor_set(v___x_703_, 3, v___x_801_);
lean_ctor_set(v___x_703_, 2, v_v_795_);
lean_ctor_set(v___x_703_, 1, v_k_794_);
lean_ctor_set(v___x_703_, 0, v___x_799_);
v___x_805_ = v___x_703_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_813_; lean_object* v_v_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v_size_695_);
v_k_813_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_813_);
v_v_814_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_814_);
lean_dec_ref(v___x_705_);
v___x_815_ = lean_unsigned_to_nat(3u);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_698_);
lean_ctor_set(v___x_779_, 2, v_v_814_);
lean_ctor_set(v___x_779_, 1, v_k_813_);
lean_ctor_set(v___x_779_, 0, v___x_700_);
v___x_817_ = v___x_779_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_k_813_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_v_814_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_l_698_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_817_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_815_);
v___x_819_ = v___x_703_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_r_699_);
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
lean_object* v_k_822_; lean_object* v_v_823_; lean_object* v___x_825_; 
v_k_822_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_822_);
v_v_823_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_823_);
lean_dec_ref(v___x_705_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 3, v_r_699_);
v___x_825_ = v___x_779_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_size_695_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_r_699_);
v___x_825_ = v_reuseFailAlloc_830_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(2u);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_825_);
lean_ctor_set(v___x_703_, 3, v_r_699_);
lean_ctor_set(v___x_703_, 2, v_v_823_);
lean_ctor_set(v___x_703_, 1, v_k_822_);
lean_ctor_set(v___x_703_, 0, v___x_826_);
v___x_828_ = v___x_703_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_822_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_823_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v___x_825_);
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
}
}
}
}
else
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_995_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v_isSharedCheck_995_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_996_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_1000_);
v___x_844_ = v_r_681_;
v_isShared_845_ = v_isSharedCheck_995_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_r_681_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_995_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_tree_847_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_696_, v_v_697_, v_l_698_, v_r_699_);
v_tree_847_ = lean_ctor_get(v___x_846_, 2);
lean_inc(v_tree_847_);
if (lean_obj_tag(v_tree_847_) == 0)
{
lean_object* v_k_848_; lean_object* v_v_849_; lean_object* v_size_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_k_848_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_848_);
v_v_849_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_849_);
lean_dec_ref(v___x_846_);
v_size_850_ = lean_ctor_get(v_tree_847_, 0);
v___x_851_ = lean_unsigned_to_nat(3u);
v___x_852_ = lean_nat_mul(v___x_851_, v_size_850_);
v___x_853_ = lean_nat_dec_lt(v___x_852_, v_size_690_);
lean_dec(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v_r_694_);
v___x_854_ = lean_nat_add(v___x_700_, v_size_690_);
v___x_855_ = lean_nat_add(v___x_854_, v_size_850_);
lean_dec(v___x_854_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_l_680_);
lean_ctor_set(v___x_844_, 2, v_v_849_);
lean_ctor_set(v___x_844_, 1, v_k_848_);
lean_ctor_set(v___x_844_, 0, v___x_855_);
v___x_857_ = v___x_844_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_tree_847_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_924_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
lean_inc(v_size_690_);
v_isSharedCheck_924_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_925_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_929_);
v___x_860_ = v_l_680_;
v_isShared_861_ = v_isSharedCheck_924_;
goto v_resetjp_859_;
}
else
{
lean_dec(v_l_680_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_924_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_size_862_; lean_object* v_size_863_; lean_object* v_k_864_; lean_object* v_v_865_; lean_object* v_l_866_; lean_object* v_r_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_size_862_ = lean_ctor_get(v_l_693_, 0);
v_size_863_ = lean_ctor_get(v_r_694_, 0);
v_k_864_ = lean_ctor_get(v_r_694_, 1);
v_v_865_ = lean_ctor_get(v_r_694_, 2);
v_l_866_ = lean_ctor_get(v_r_694_, 3);
v_r_867_ = lean_ctor_get(v_r_694_, 4);
v___x_868_ = lean_unsigned_to_nat(2u);
v___x_869_ = lean_nat_mul(v___x_868_, v_size_862_);
v___x_870_ = lean_nat_dec_lt(v_size_863_, v___x_869_);
lean_dec(v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_908_; 
lean_inc(v_r_867_);
lean_inc(v_l_866_);
lean_inc(v_v_865_);
lean_inc(v_k_864_);
lean_del_object(v___x_860_);
v_isSharedCheck_908_ = !lean_is_exclusive(v_r_694_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_909_ = lean_ctor_get(v_r_694_, 4);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_r_694_, 3);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_r_694_, 2);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_r_694_, 1);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_r_694_, 0);
lean_dec(v_unused_913_);
v___x_872_ = v_r_694_;
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
else
{
lean_dec(v_r_694_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___x_896_; lean_object* v___y_898_; 
v___x_874_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_875_ = lean_nat_add(v___x_874_, v_size_850_);
lean_dec(v___x_874_);
v___x_896_ = lean_nat_add(v___x_700_, v_size_862_);
if (lean_obj_tag(v_l_866_) == 0)
{
lean_object* v_size_906_; 
v_size_906_ = lean_ctor_get(v_l_866_, 0);
lean_inc(v_size_906_);
v___y_898_ = v_size_906_;
goto v___jp_897_;
}
else
{
lean_object* v___x_907_; 
v___x_907_ = lean_unsigned_to_nat(0u);
v___y_898_ = v___x_907_;
goto v___jp_897_;
}
v___jp_876_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_nat_add(v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_inc_ref(v_tree_847_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 4, v_tree_847_);
lean_ctor_set(v___x_872_, 3, v_r_867_);
lean_ctor_set(v___x_872_, 2, v_v_849_);
lean_ctor_set(v___x_872_, 1, v_k_848_);
lean_ctor_set(v___x_872_, 0, v___x_880_);
v___x_882_ = v___x_872_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_r_867_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_tree_847_);
v___x_882_ = v_reuseFailAlloc_895_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_isSharedCheck_889_ = !lean_is_exclusive(v_tree_847_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_890_ = lean_ctor_get(v_tree_847_, 4);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_tree_847_, 3);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_tree_847_, 2);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_tree_847_, 1);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_tree_847_, 0);
lean_dec(v_unused_894_);
v___x_884_ = v_tree_847_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_tree_847_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 4, v___x_882_);
lean_ctor_set(v___x_884_, 3, v___y_877_);
lean_ctor_set(v___x_884_, 2, v_v_865_);
lean_ctor_set(v___x_884_, 1, v_k_864_);
lean_ctor_set(v___x_884_, 0, v___x_875_);
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_864_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_865_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___y_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v___x_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_nat_add(v___x_896_, v___y_898_);
lean_dec(v___y_898_);
lean_dec(v___x_896_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_l_866_);
lean_ctor_set(v___x_844_, 3, v_l_693_);
lean_ctor_set(v___x_844_, 2, v_v_692_);
lean_ctor_set(v___x_844_, 1, v_k_691_);
lean_ctor_set(v___x_844_, 0, v___x_899_);
v___x_901_ = v___x_844_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_l_866_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; 
v___x_902_ = lean_nat_add(v___x_700_, v_size_850_);
if (lean_obj_tag(v_r_867_) == 0)
{
lean_object* v_size_903_; 
v_size_903_ = lean_ctor_get(v_r_867_, 0);
lean_inc(v_size_903_);
v___y_877_ = v___x_901_;
v___y_878_ = v___x_902_;
v___y_879_ = v_size_903_;
goto v___jp_876_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___y_877_ = v___x_901_;
v___y_878_ = v___x_902_;
v___y_879_ = v___x_904_;
goto v___jp_876_;
}
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_914_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_915_ = lean_nat_add(v___x_914_, v_size_850_);
lean_dec(v___x_914_);
v___x_916_ = lean_nat_add(v___x_700_, v_size_850_);
v___x_917_ = lean_nat_add(v___x_916_, v_size_863_);
lean_dec(v___x_916_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_849_);
lean_ctor_set(v___x_844_, 1, v_k_848_);
lean_ctor_set(v___x_844_, 0, v___x_917_);
v___x_919_ = v___x_844_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_tree_847_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 4, v___x_919_);
lean_ctor_set(v___x_860_, 0, v___x_915_);
v___x_921_ = v___x_860_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_693_) == 0)
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_953_; 
lean_inc_ref(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
lean_inc(v_size_690_);
v_isSharedCheck_953_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; 
v_unused_954_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_958_);
v___x_931_ = v_l_680_;
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
else
{
lean_dec(v_l_680_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
if (lean_obj_tag(v_r_694_) == 0)
{
lean_object* v_k_933_; lean_object* v_v_934_; lean_object* v_size_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v_k_933_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_933_);
v_v_934_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_934_);
lean_dec_ref(v___x_846_);
v_size_935_ = lean_ctor_get(v_r_694_, 0);
v___x_936_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_937_ = lean_nat_add(v___x_700_, v_size_935_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_934_);
lean_ctor_set(v___x_844_, 1, v_k_933_);
lean_ctor_set(v___x_844_, 0, v___x_937_);
v___x_939_ = v___x_844_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_k_933_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_v_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_tree_847_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_939_);
lean_ctor_set(v___x_931_, 0, v___x_936_);
v___x_941_ = v___x_931_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v_k_944_; lean_object* v_v_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_dec(v_size_690_);
v_k_944_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_944_);
v_v_945_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_945_);
lean_dec_ref(v___x_846_);
v___x_946_ = lean_unsigned_to_nat(3u);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_r_694_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_945_);
lean_ctor_set(v___x_844_, 1, v_k_944_);
lean_ctor_set(v___x_844_, 0, v___x_700_);
v___x_948_ = v___x_844_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_r_694_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_948_);
lean_ctor_set(v___x_931_, 0, v___x_946_);
v___x_950_ = v___x_931_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v___x_948_);
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
else
{
if (lean_obj_tag(v_r_694_) == 0)
{
lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; 
v_unused_984_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_988_);
v___x_960_ = v_l_680_;
v_isShared_961_ = v_isSharedCheck_983_;
goto v_resetjp_959_;
}
else
{
lean_dec(v_l_680_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_983_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_k_962_; lean_object* v_v_963_; lean_object* v_k_964_; lean_object* v_v_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_979_; 
v_k_962_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_962_);
v_v_963_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_963_);
lean_dec_ref(v___x_846_);
v_k_964_ = lean_ctor_get(v_r_694_, 1);
v_v_965_ = lean_ctor_get(v_r_694_, 2);
v_isSharedCheck_979_ = !lean_is_exclusive(v_r_694_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; 
v_unused_980_ = lean_ctor_get(v_r_694_, 4);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_r_694_, 3);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_r_694_, 0);
lean_dec(v_unused_982_);
v___x_967_ = v_r_694_;
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_v_965_);
lean_inc(v_k_964_);
lean_dec(v_r_694_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_unsigned_to_nat(3u);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v_l_693_);
lean_ctor_set(v___x_967_, 3, v_l_693_);
lean_ctor_set(v___x_967_, 2, v_v_692_);
lean_ctor_set(v___x_967_, 1, v_k_691_);
lean_ctor_set(v___x_967_, 0, v___x_700_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_l_693_);
v___x_971_ = v_reuseFailAlloc_978_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_l_693_);
lean_ctor_set(v___x_844_, 3, v_l_693_);
lean_ctor_set(v___x_844_, 2, v_v_963_);
lean_ctor_set(v___x_844_, 1, v_k_962_);
lean_ctor_set(v___x_844_, 0, v___x_700_);
v___x_973_ = v___x_844_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_l_693_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v___x_973_);
lean_ctor_set(v___x_960_, 3, v___x_971_);
lean_ctor_set(v___x_960_, 2, v_v_965_);
lean_ctor_set(v___x_960_, 1, v_k_964_);
lean_ctor_set(v___x_960_, 0, v___x_969_);
v___x_975_ = v___x_960_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_965_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
else
{
lean_object* v_k_989_; lean_object* v_v_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v_k_989_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_989_);
v_v_990_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_990_);
lean_dec_ref(v___x_846_);
v___x_991_ = lean_unsigned_to_nat(2u);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_r_694_);
lean_ctor_set(v___x_844_, 3, v_l_680_);
lean_ctor_set(v___x_844_, 2, v_v_990_);
lean_ctor_set(v___x_844_, 1, v_k_989_);
lean_ctor_set(v___x_844_, 0, v___x_991_);
v___x_993_ = v___x_844_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_989_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_r_694_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
}
else
{
return v_l_680_;
}
}
else
{
return v_r_681_;
}
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1003_; 
v_val_1001_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_1001_);
lean_dec_ref(v___x_689_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 2, v_val_1001_);
lean_ctor_set(v___x_683_, 1, v_k_675_);
v___x_1003_ = v___x_683_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_size_677_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_k_675_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_val_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_r_681_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
default: 
{
lean_object* v_impl_1005_; lean_object* v___x_1006_; 
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
v_impl_1005_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_674_, v_k_675_, v_r_681_);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_678_, v_v_679_, v_l_680_, v_impl_1005_);
return v___x_1006_;
}
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_674_, v___x_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec(v_k_675_);
return v_t_676_;
}
else
{
lean_object* v_val_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_val_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_val_1010_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_k_675_);
lean_ctor_set(v___x_1012_, 2, v_val_1010_);
lean_ctor_set(v___x_1012_, 3, v_t_676_);
lean_ctor_set(v___x_1012_, 4, v_t_676_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1013_, lean_object* v_i_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_keys_1013_);
v___x_1017_ = lean_nat_dec_lt(v_i_1014_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_i_1014_);
return v___x_1017_;
}
else
{
lean_object* v_k_x27_1018_; uint8_t v___x_1019_; 
v_k_x27_1018_ = lean_array_fget_borrowed(v_keys_1013_, v_i_1014_);
v___x_1019_ = lean_name_eq(v_k_1015_, v_k_x27_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_i_1014_, v___x_1020_);
lean_dec(v_i_1014_);
v_i_1014_ = v___x_1021_;
goto _start;
}
else
{
lean_dec(v_i_1014_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1023_, v_i_1024_, v_k_1025_);
lean_dec(v_k_1025_);
lean_dec_ref(v_keys_1023_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; 
v___x_1028_ = ((size_t)5ULL);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_shift_left(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; 
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0);
v___x_1033_ = lean_usize_sub(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1034_, size_t v_x_1035_, lean_object* v_x_1036_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v_es_1037_; lean_object* v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v_j_1042_; lean_object* v___x_1043_; 
v_es_1037_ = lean_ctor_get(v_x_1034_, 0);
v___x_1038_ = lean_box(2);
v___x_1039_ = ((size_t)5ULL);
v___x_1040_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1041_ = lean_usize_land(v_x_1035_, v___x_1040_);
v_j_1042_ = lean_usize_to_nat(v___x_1041_);
v___x_1043_ = lean_array_get_borrowed(v___x_1038_, v_es_1037_, v_j_1042_);
lean_dec(v_j_1042_);
switch(lean_obj_tag(v___x_1043_))
{
case 0:
{
lean_object* v_key_1044_; uint8_t v___x_1045_; 
v_key_1044_ = lean_ctor_get(v___x_1043_, 0);
v___x_1045_ = lean_name_eq(v_x_1036_, v_key_1044_);
return v___x_1045_;
}
case 1:
{
lean_object* v_node_1046_; size_t v___x_1047_; 
v_node_1046_ = lean_ctor_get(v___x_1043_, 0);
v___x_1047_ = lean_usize_shift_right(v_x_1035_, v___x_1039_);
v_x_1034_ = v_node_1046_;
v_x_1035_ = v___x_1047_;
goto _start;
}
default: 
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
return v___x_1049_;
}
}
}
else
{
lean_object* v_ks_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_ks_1050_ = lean_ctor_get(v_x_1034_, 0);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1050_, v___x_1051_, v_x_1036_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
size_t v_x_4172__boxed_1056_; uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_x_4172__boxed_1056_ = lean_unbox_usize(v_x_1054_);
lean_dec(v_x_1054_);
v_res_1057_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1053_, v_x_4172__boxed_1056_, v_x_1055_);
lean_dec(v_x_1055_);
lean_dec_ref(v_x_1053_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1059_; uint64_t v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1723u);
v___x_1060_ = lean_uint64_of_nat(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
uint64_t v___y_1064_; 
if (lean_obj_tag(v_x_1062_) == 0)
{
uint64_t v___x_1067_; 
v___x_1067_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1064_ = v___x_1067_;
goto v___jp_1063_;
}
else
{
uint64_t v_hash_1068_; 
v_hash_1068_ = lean_ctor_get_uint64(v_x_1062_, sizeof(void*)*2);
v___y_1064_ = v_hash_1068_;
goto v___jp_1063_;
}
v___jp_1063_:
{
size_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_uint64_to_usize(v___y_1064_);
v___x_1066_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1061_, v___x_1065_, v_x_1062_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1069_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec_ref(v_x_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1073_, lean_object* v_a_1074_, uint8_t v___x_1075_, lean_object* v_x_1076_, lean_object* v_____s_1077_){
_start:
{
lean_object* v_fst_1078_; lean_object* v_kinds_1079_; uint8_t v___x_1080_; 
v_fst_1078_ = lean_ctor_get(v_x_1076_, 0);
lean_inc(v_fst_1078_);
lean_dec_ref(v_x_1076_);
v_kinds_1079_ = lean_ctor_get(v_tactics_1073_, 1);
v___x_1080_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1079_, v_fst_1078_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec(v_fst_1078_);
lean_dec(v_a_1074_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_____s_1077_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_Name_toString(v_a_1074_, v___x_1075_);
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1082_, v_fst_1078_, v_____s_1077_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1085_, lean_object* v_a_1086_, lean_object* v___x_1087_, lean_object* v_x_1088_, lean_object* v_____s_1089_){
_start:
{
uint8_t v___x_4240__boxed_1090_; lean_object* v_res_1091_; 
v___x_4240__boxed_1090_ = lean_unbox(v___x_1087_);
v_res_1091_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1085_, v_a_1086_, v___x_4240__boxed_1090_, v_x_1088_, v_____s_1089_);
lean_dec_ref(v_tactics_1085_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1092_, lean_object* v_keys_1093_, lean_object* v_vals_1094_, lean_object* v_i_1095_, lean_object* v_acc_1096_){
_start:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_array_get_size(v_keys_1093_);
v___x_1098_ = lean_nat_dec_lt(v_i_1095_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v_i_1095_);
lean_dec_ref(v_f_1092_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_acc_1096_);
return v___x_1099_;
}
else
{
lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v___x_1102_; 
v_k_1100_ = lean_array_fget_borrowed(v_keys_1093_, v_i_1095_);
v_v_1101_ = lean_array_fget_borrowed(v_vals_1094_, v_i_1095_);
lean_inc_ref(v_f_1092_);
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
v___x_1102_ = lean_apply_3(v_f_1092_, v_acc_1096_, v_k_1100_, v_v_1101_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec(v_i_1095_);
lean_dec_ref(v_f_1092_);
return v___x_1102_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_i_1095_, v___x_1104_);
lean_dec(v_i_1095_);
v_i_1095_ = v___x_1105_;
v_acc_1096_ = v_a_1103_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1107_, lean_object* v_keys_1108_, lean_object* v_vals_1109_, lean_object* v_i_1110_, lean_object* v_acc_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1107_, v_keys_1108_, v_vals_1109_, v_i_1110_, v_acc_1111_);
lean_dec_ref(v_vals_1109_);
lean_dec_ref(v_keys_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
lean_object* v_es_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1136_; 
v_es_1116_ = lean_ctor_get(v_x_1114_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1114_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1118_ = v_x_1114_;
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_es_1116_);
lean_dec(v_x_1114_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_array_get_size(v_es_1116_);
v___x_1122_ = lean_nat_dec_lt(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v_es_1116_);
lean_dec_ref(v_f_1113_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v_x_1115_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_x_1115_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_nat_dec_le(v___x_1121_, v___x_1121_);
if (v___x_1126_ == 0)
{
if (v___x_1122_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_es_1116_);
lean_dec_ref(v_f_1113_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v_x_1115_);
v___x_1128_ = v___x_1118_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_x_1115_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_1118_);
v___x_1130_ = ((size_t)0ULL);
v___x_1131_ = lean_usize_of_nat(v___x_1121_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1113_, v_es_1116_, v___x_1130_, v___x_1131_, v_x_1115_);
lean_dec_ref(v_es_1116_);
return v___x_1132_;
}
}
else
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_1118_);
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = lean_usize_of_nat(v___x_1121_);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1113_, v_es_1116_, v___x_1133_, v___x_1134_, v_x_1115_);
lean_dec_ref(v_es_1116_);
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_ks_1137_; lean_object* v_vs_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_ks_1137_ = lean_ctor_get(v_x_1114_, 0);
lean_inc_ref(v_ks_1137_);
v_vs_1138_ = lean_ctor_get(v_x_1114_, 1);
lean_inc_ref(v_vs_1138_);
lean_dec_ref(v_x_1114_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1113_, v_ks_1137_, v_vs_1138_, v___x_1139_, v_x_1115_);
lean_dec_ref(v_vs_1138_);
lean_dec_ref(v_ks_1137_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1141_, lean_object* v_as_1142_, size_t v_i_1143_, size_t v_stop_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_a_1147_; lean_object* v___y_1152_; uint8_t v___x_1154_; 
v___x_1154_ = lean_usize_dec_eq(v_i_1143_, v_stop_1144_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_array_uget_borrowed(v_as_1142_, v_i_1143_);
switch(lean_obj_tag(v___x_1155_))
{
case 0:
{
lean_object* v_key_1156_; lean_object* v_val_1157_; lean_object* v___x_1158_; 
v_key_1156_ = lean_ctor_get(v___x_1155_, 0);
v_val_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc_ref(v_f_1141_);
lean_inc(v_val_1157_);
lean_inc(v_key_1156_);
v___x_1158_ = lean_apply_3(v_f_1141_, v_b_1145_, v_key_1156_, v_val_1157_);
v___y_1152_ = v___x_1158_;
goto v___jp_1151_;
}
case 1:
{
lean_object* v_node_1159_; lean_object* v___x_1160_; 
v_node_1159_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_node_1159_);
lean_inc_ref(v_f_1141_);
v___x_1160_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1141_, v_node_1159_, v_b_1145_);
v___y_1152_ = v___x_1160_;
goto v___jp_1151_;
}
default: 
{
v_a_1147_ = v_b_1145_;
goto v___jp_1146_;
}
}
}
else
{
lean_object* v___x_1161_; 
lean_dec_ref(v_f_1141_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1145_);
return v___x_1161_;
}
v___jp_1146_:
{
size_t v___x_1148_; size_t v___x_1149_; 
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1143_, v___x_1148_);
v_i_1143_ = v___x_1149_;
v_b_1145_ = v_a_1147_;
goto _start;
}
v___jp_1151_:
{
if (lean_obj_tag(v___y_1152_) == 0)
{
lean_dec_ref(v_f_1141_);
return v___y_1152_;
}
else
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_ctor_get(v___y_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___y_1152_);
v_a_1147_ = v_a_1153_;
goto v___jp_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1162_, lean_object* v_as_1163_, lean_object* v_i_1164_, lean_object* v_stop_1165_, lean_object* v_b_1166_){
_start:
{
size_t v_i_boxed_1167_; size_t v_stop_boxed_1168_; lean_object* v_res_1169_; 
v_i_boxed_1167_ = lean_unbox_usize(v_i_1164_);
lean_dec(v_i_1164_);
v_stop_boxed_1168_ = lean_unbox_usize(v_stop_1165_);
lean_dec(v_stop_1165_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1162_, v_as_1163_, v_i_boxed_1167_, v_stop_boxed_1168_, v_b_1166_);
lean_dec_ref(v_as_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1170_, lean_object* v_s_1171_, lean_object* v_a_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_a_1172_);
lean_ctor_set(v___x_1174_, 1, v_b_1173_);
v___x_1175_ = lean_apply_2(v_f_1170_, v___x_1174_, v_s_1171_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
v_a_1184_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1175_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1175_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1192_, lean_object* v_init_1193_, lean_object* v_f_1194_){
_start:
{
lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v_a_1197_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1195_, 0, v_f_1194_);
v___x_1196_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1195_, v_map_1192_, v_init_1193_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
return v_a_1197_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1198_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1201_, lean_object* v_a_1202_, uint8_t v___x_1203_, lean_object* v_as_x27_1204_, lean_object* v_b_1205_){
_start:
{
if (lean_obj_tag(v_as_x27_1204_) == 0)
{
lean_dec(v_a_1202_);
lean_dec_ref(v_tactics_1201_);
return v_b_1205_;
}
else
{
lean_object* v_head_1206_; lean_object* v_fst_1207_; lean_object* v_info_1208_; lean_object* v_tail_1209_; lean_object* v_collectKinds_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_head_1206_ = lean_ctor_get(v_as_x27_1204_, 0);
v_fst_1207_ = lean_ctor_get(v_head_1206_, 0);
v_info_1208_ = lean_ctor_get(v_fst_1207_, 0);
lean_inc_ref(v_info_1208_);
v_tail_1209_ = lean_ctor_get(v_as_x27_1204_, 1);
lean_inc(v_tail_1209_);
lean_dec_ref(v_as_x27_1204_);
v_collectKinds_1210_ = lean_ctor_get(v_info_1208_, 1);
lean_inc_ref(v_collectKinds_1210_);
lean_dec_ref(v_info_1208_);
v___x_1211_ = lean_box(v___x_1203_);
lean_inc(v_a_1202_);
lean_inc_ref(v_tactics_1201_);
v___f_1212_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1212_, 0, v_tactics_1201_);
lean_closure_set(v___f_1212_, 1, v_a_1202_);
lean_closure_set(v___f_1212_, 2, v___x_1211_);
v___x_1213_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
v___x_1214_ = lean_apply_1(v_collectKinds_1210_, v___x_1213_);
v___x_1215_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1214_, v_b_1205_, v___f_1212_);
v_as_x27_1204_ = v_tail_1209_;
v_b_1205_ = v___x_1215_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1217_, lean_object* v_a_1218_, lean_object* v___x_1219_, lean_object* v_as_x27_1220_, lean_object* v_b_1221_){
_start:
{
uint8_t v___x_4414__boxed_1222_; lean_object* v_res_1223_; 
v___x_4414__boxed_1222_ = lean_unbox(v___x_1219_);
v_res_1223_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1217_, v_a_1218_, v___x_4414__boxed_1222_, v_as_x27_1220_, v_b_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1227_, lean_object* v_init_1228_, lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 0)
{
lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v_l_1232_; lean_object* v_r_1233_; lean_object* v___x_1234_; lean_object* v_a_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_k_1230_ = lean_ctor_get(v_x_1229_, 1);
lean_inc(v_k_1230_);
v_v_1231_ = lean_ctor_get(v_x_1229_, 2);
lean_inc(v_v_1231_);
v_l_1232_ = lean_ctor_get(v_x_1229_, 3);
lean_inc(v_l_1232_);
v_r_1233_ = lean_ctor_get(v_x_1229_, 4);
lean_inc(v_r_1233_);
lean_dec_ref(v_x_1229_);
lean_inc_ref(v_tactics_1227_);
v___x_1234_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1227_, v_init_1228_, v_l_1232_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
v___x_1236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1237_ = lean_name_eq(v_k_1230_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec_ref(v___x_1234_);
lean_inc_ref(v_tactics_1227_);
v___x_1238_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1227_, v_k_1230_, v___x_1237_, v_v_1231_, v_a_1235_);
v_init_1228_ = v___x_1238_;
v_x_1229_ = v_r_1233_;
goto _start;
}
else
{
lean_object* v_a_1240_; 
lean_dec(v_a_1235_);
lean_dec(v_v_1231_);
lean_dec(v_k_1230_);
v_a_1240_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1234_);
v_init_1228_ = v_a_1240_;
v_x_1229_ = v_r_1233_;
goto _start;
}
}
else
{
lean_object* v___x_1242_; 
lean_dec_ref(v_tactics_1227_);
v___x_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1242_, 0, v_init_1228_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1243_, lean_object* v_table_1244_, lean_object* v_firsts_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v_a_1247_; 
v___x_1246_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1243_, v_firsts_1245_, v_table_1244_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
return v_a_1247_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1249_, v_x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1252_, v_x_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec_ref(v_x_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1257_, lean_object* v_k_1258_, lean_object* v_t_1259_, lean_object* v_hl_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1257_, v_k_1258_, v_t_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_map_1264_, lean_object* v_init_1265_, lean_object* v_f_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1264_, v_init_1265_, v_f_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1268_, lean_object* v_a_1269_, uint8_t v___x_1270_, lean_object* v_as_1271_, lean_object* v_as_x27_1272_, lean_object* v_b_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1268_, v_a_1269_, v___x_1270_, v_as_x27_1272_, v_b_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1276_, lean_object* v_a_1277_, lean_object* v___x_1278_, lean_object* v_as_1279_, lean_object* v_as_x27_1280_, lean_object* v_b_1281_, lean_object* v_a_1282_){
_start:
{
uint8_t v___x_4497__boxed_1283_; lean_object* v_res_1284_; 
v___x_4497__boxed_1283_ = lean_unbox(v___x_1278_);
v_res_1284_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1276_, v_a_1277_, v___x_4497__boxed_1283_, v_as_1279_, v_as_x27_1280_, v_b_1281_, v_a_1282_);
lean_dec(v_as_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1285_, lean_object* v_x_1286_, size_t v_x_1287_, lean_object* v_x_1288_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1286_, v_x_1287_, v_x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_){
_start:
{
size_t v_x_4506__boxed_1294_; uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_x_4506__boxed_1294_ = lean_unbox_usize(v_x_1292_);
lean_dec(v_x_1292_);
v_res_1295_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1290_, v_x_1291_, v_x_4506__boxed_1294_, v_x_1293_);
lean_dec(v_x_1293_);
lean_dec_ref(v_x_1291_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1297_, lean_object* v_f_1298_, lean_object* v_init_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1298_, v_map_1297_, v_init_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1301_, lean_object* v_00_u03c3_1302_, lean_object* v_00_u03b2_1303_, lean_object* v_map_1304_, lean_object* v_f_1305_, lean_object* v_init_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1305_, v_map_1304_, v_init_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1308_, lean_object* v_keys_1309_, lean_object* v_vals_1310_, lean_object* v_heq_1311_, lean_object* v_i_1312_, lean_object* v_k_1313_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1309_, v_i_1312_, v_k_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1315_, lean_object* v_keys_1316_, lean_object* v_vals_1317_, lean_object* v_heq_1318_, lean_object* v_i_1319_, lean_object* v_k_1320_){
_start:
{
uint8_t v_res_1321_; lean_object* v_r_1322_; 
v_res_1321_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1315_, v_keys_1316_, v_vals_1317_, v_heq_1318_, v_i_1319_, v_k_1320_);
lean_dec(v_k_1320_);
lean_dec_ref(v_vals_1317_);
lean_dec_ref(v_keys_1316_);
v_r_1322_ = lean_box(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1323_, lean_object* v_00_u03c3_1324_, lean_object* v_00_u03b1_1325_, lean_object* v_00_u03b2_1326_, lean_object* v_f_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1327_, v_x_1328_, v_x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_00_u03c3_1333_, lean_object* v_00_u03c3_1334_, lean_object* v_f_1335_, lean_object* v_as_1336_, size_t v_i_1337_, size_t v_stop_1338_, lean_object* v_b_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1335_, v_as_1336_, v_i_1337_, v_stop_1338_, v_b_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_00_u03c3_1343_, lean_object* v_00_u03c3_1344_, lean_object* v_f_1345_, lean_object* v_as_1346_, lean_object* v_i_1347_, lean_object* v_stop_1348_, lean_object* v_b_1349_){
_start:
{
size_t v_i_boxed_1350_; size_t v_stop_boxed_1351_; lean_object* v_res_1352_; 
v_i_boxed_1350_ = lean_unbox_usize(v_i_1347_);
lean_dec(v_i_1347_);
v_stop_boxed_1351_ = lean_unbox_usize(v_stop_1348_);
lean_dec(v_stop_1348_);
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1341_, v_00_u03b2_1342_, v_00_u03c3_1343_, v_00_u03c3_1344_, v_f_1345_, v_as_1346_, v_i_boxed_1350_, v_stop_boxed_1351_, v_b_1349_);
lean_dec_ref(v_as_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1353_, lean_object* v_00_u03c3_1354_, lean_object* v_00_u03b1_1355_, lean_object* v_00_u03b2_1356_, lean_object* v_f_1357_, lean_object* v_keys_1358_, lean_object* v_vals_1359_, lean_object* v_heq_1360_, lean_object* v_i_1361_, lean_object* v_acc_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1357_, v_keys_1358_, v_vals_1359_, v_i_1361_, v_acc_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1364_, lean_object* v_00_u03c3_1365_, lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_f_1368_, lean_object* v_keys_1369_, lean_object* v_vals_1370_, lean_object* v_heq_1371_, lean_object* v_i_1372_, lean_object* v_acc_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1364_, v_00_u03c3_1365_, v_00_u03b1_1366_, v_00_u03b2_1367_, v_f_1368_, v_keys_1369_, v_vals_1370_, v_heq_1371_, v_i_1372_, v_acc_1373_);
lean_dec_ref(v_vals_1370_);
lean_dec_ref(v_keys_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1375_, lean_object* v_x2_1376_){
_start:
{
lean_object* v_fst_1377_; lean_object* v_snd_1378_; lean_object* v___x_1379_; 
v_fst_1377_ = lean_ctor_get(v_x2_1376_, 0);
lean_inc(v_fst_1377_);
v_snd_1378_ = lean_ctor_get(v_x2_1376_, 1);
lean_inc(v_snd_1378_);
lean_dec_ref(v_x2_1376_);
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1377_, v_snd_1378_, v_x1_1375_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1399_, lean_object* v_x1_1400_, lean_object* v_x2_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_array_get_size(v_x2_1401_);
v___x_1404_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1405_ = lean_nat_dec_lt(v___x_1402_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v_x2_1401_);
lean_dec_ref(v___f_1399_);
return v_x1_1400_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_le(v___x_1403_, v___x_1403_);
if (v___x_1406_ == 0)
{
if (v___x_1405_ == 0)
{
lean_dec_ref(v_x2_1401_);
lean_dec_ref(v___f_1399_);
return v_x1_1400_;
}
else
{
size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = lean_usize_of_nat(v___x_1403_);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1404_, v___f_1399_, v_x2_1401_, v___x_1407_, v___x_1408_, v_x1_1400_);
return v___x_1409_;
}
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1403_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1404_, v___f_1399_, v_x2_1401_, v___x_1410_, v___x_1411_, v_x1_1400_);
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v_toPure_1421_, lean_object* v___f_1422_, lean_object* v_env_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v_ext_1425_; lean_object* v_toEnvExtension_1426_; lean_object* v_asyncMode_1427_; lean_object* v___x_1428_; lean_object* v_categories_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1424_ = l_Lean_Parser_parserExtension;
v_ext_1425_ = lean_ctor_get(v___x_1424_, 1);
v_toEnvExtension_1426_ = lean_ctor_get(v_ext_1425_, 0);
v_asyncMode_1427_ = lean_ctor_get(v_toEnvExtension_1426_, 2);
lean_inc_ref(v_env_1423_);
v___x_1428_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1416_, v___x_1424_, v_env_1423_, v_asyncMode_1427_);
v_categories_1429_ = lean_ctor_get(v___x_1428_, 2);
lean_inc_ref(v_categories_1429_);
lean_dec(v___x_1428_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1431_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1417_, v___x_1418_, v_categories_1429_, v___x_1430_);
if (lean_obj_tag(v___x_1431_) == 1)
{
lean_object* v_val_1432_; lean_object* v___y_1434_; lean_object* v___x_1441_; lean_object* v_toEnvExtension_1442_; lean_object* v_exportEntriesFn_1443_; lean_object* v_asyncMode_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_importedEntries_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_exported_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_val_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1432_);
lean_dec_ref(v___x_1431_);
v___x_1441_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1442_ = lean_ctor_get(v___x_1441_, 0);
v_exportEntriesFn_1443_ = lean_ctor_get(v___x_1441_, 4);
v_asyncMode_1444_ = lean_ctor_get(v_toEnvExtension_1442_, 2);
v___x_1445_ = lean_box(0);
lean_inc_ref_n(v_env_1423_, 2);
v___x_1446_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1419_, v_toEnvExtension_1442_, v_env_1423_, v_asyncMode_1444_, v___x_1445_);
v_importedEntries_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_importedEntries_1447_);
lean_dec(v___x_1446_);
v___x_1448_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1420_, v___x_1441_, v_env_1423_, v_asyncMode_1444_, v___x_1445_);
lean_inc_ref(v_exportEntriesFn_1443_);
v___x_1449_ = lean_apply_2(v_exportEntriesFn_1443_, v_env_1423_, v___x_1448_);
v_exported_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_exported_1450_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = lean_box(1);
v___x_1452_ = lean_array_push(v_importedEntries_1447_, v_exported_1450_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_array_get_size(v___x_1452_);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1456_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
if (v___x_1456_ == 0)
{
lean_dec_ref(v___x_1452_);
lean_dec_ref(v___f_1422_);
v___y_1434_ = v___x_1451_;
goto v___jp_1433_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
if (v___x_1457_ == 0)
{
if (v___x_1456_ == 0)
{
lean_dec_ref(v___x_1452_);
lean_dec_ref(v___f_1422_);
v___y_1434_ = v___x_1451_;
goto v___jp_1433_;
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1454_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1455_, v___f_1422_, v___x_1452_, v___x_1458_, v___x_1459_, v___x_1451_);
v___y_1434_ = v___x_1460_;
goto v___jp_1433_;
}
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = lean_usize_of_nat(v___x_1454_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1455_, v___f_1422_, v___x_1452_, v___x_1461_, v___x_1462_, v___x_1451_);
v___y_1434_ = v___x_1463_;
goto v___jp_1433_;
}
}
v___jp_1433_:
{
lean_object* v_tables_1435_; lean_object* v_leadingTable_1436_; lean_object* v_trailingTable_1437_; lean_object* v_firstTokens_1438_; lean_object* v_firstTokens_1439_; lean_object* v___x_1440_; 
v_tables_1435_ = lean_ctor_get(v_val_1432_, 2);
v_leadingTable_1436_ = lean_ctor_get(v_tables_1435_, 0);
v_trailingTable_1437_ = lean_ctor_get(v_tables_1435_, 2);
lean_inc(v_trailingTable_1437_);
lean_inc(v_leadingTable_1436_);
lean_inc(v_val_1432_);
v_firstTokens_1438_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1432_, v_leadingTable_1436_, v___y_1434_);
v_firstTokens_1439_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1432_, v_trailingTable_1437_, v_firstTokens_1438_);
v___x_1440_ = lean_apply_2(v_toPure_1421_, lean_box(0), v_firstTokens_1439_);
return v___x_1440_;
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec(v___x_1431_);
lean_dec_ref(v_env_1423_);
lean_dec_ref(v___f_1422_);
lean_dec(v___x_1420_);
v___x_1464_ = lean_box(1);
v___x_1465_ = lean_apply_2(v_toPure_1421_, lean_box(0), v___x_1464_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1466_, lean_object* v___x_1467_, lean_object* v___x_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v_toPure_1471_, lean_object* v___f_1472_, lean_object* v_env_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1466_, v___x_1467_, v___x_1468_, v___x_1469_, v___x_1470_, v_toPure_1471_, v___f_1472_, v_env_1473_);
lean_dec_ref(v___x_1469_);
lean_dec_ref(v___x_1466_);
return v_res_1474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_box(1);
v___x_1479_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1482_, lean_object* v_inst_1483_){
_start:
{
lean_object* v_toApplicative_1484_; lean_object* v_toBind_1485_; lean_object* v_getEnv_1486_; lean_object* v_toPure_1487_; lean_object* v___f_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___f_1494_; lean_object* v___x_1495_; 
v_toApplicative_1484_ = lean_ctor_get(v_inst_1482_, 0);
lean_inc_ref(v_toApplicative_1484_);
v_toBind_1485_ = lean_ctor_get(v_inst_1482_, 1);
lean_inc(v_toBind_1485_);
lean_dec_ref(v_inst_1482_);
v_getEnv_1486_ = lean_ctor_get(v_inst_1483_, 0);
lean_inc(v_getEnv_1486_);
lean_dec_ref(v_inst_1483_);
v_toPure_1487_ = lean_ctor_get(v_toApplicative_1484_, 1);
lean_inc(v_toPure_1487_);
lean_dec_ref(v_toApplicative_1484_);
v___f_1488_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1489_ = lean_box(1);
v___x_1490_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1493_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1494_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1494_, 0, v___x_1493_);
lean_closure_set(v___f_1494_, 1, v___x_1491_);
lean_closure_set(v___f_1494_, 2, v___x_1492_);
lean_closure_set(v___f_1494_, 3, v___x_1490_);
lean_closure_set(v___f_1494_, 4, v___x_1489_);
lean_closure_set(v___f_1494_, 5, v_toPure_1487_);
lean_closure_set(v___f_1494_, 6, v___f_1488_);
v___x_1495_ = lean_apply_4(v_toBind_1485_, lean_box(0), lean_box(0), v_getEnv_1486_, v___f_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1497_, v_inst_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_x_1500_, lean_object* v_y_1501_){
_start:
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_nat_dec_lt(v_x_1500_, v_y_1501_);
if (v___x_1502_ == 0)
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_nat_dec_eq(v_x_1500_, v_y_1501_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
v___x_1504_ = 2;
return v___x_1504_;
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = 1;
return v___x_1505_;
}
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = 0;
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed(lean_object* v_x_1507_, lean_object* v_y_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(v_x_1507_, v_y_1508_);
lean_dec(v_y_1508_);
lean_dec(v_x_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v___f_1511_, lean_object* v_a_1512_, lean_object* v_x_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_fst_1515_; lean_object* v_snd_1516_; lean_object* v_r_1517_; lean_object* v___x_1518_; 
v_fst_1515_ = lean_ctor_get(v_a_1512_, 0);
lean_inc(v_fst_1515_);
v_snd_1516_ = lean_ctor_get(v_a_1512_, 1);
lean_inc(v_snd_1516_);
lean_dec_ref(v_a_1512_);
v_r_1517_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_1511_, v_fst_1515_, v_snd_1516_, v___y_1514_);
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_r_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2(lean_object* v_n_1525_, lean_object* v___y_1526_, lean_object* v___f_1527_, lean_object* v_toPure_1528_, lean_object* v_firsts_1529_, lean_object* v_____do__lift_1530_){
_start:
{
lean_object* v___y_1532_; lean_object* v_val_1564_; 
if (lean_obj_tag(v_____do__lift_1530_) == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3));
lean_inc(v_n_1525_);
v___x_1567_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1566_, v_firsts_1529_, v_n_1525_);
if (lean_obj_tag(v___x_1567_) == 0)
{
uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = 1;
lean_inc(v_n_1525_);
v___x_1569_ = l_Lean_Name_toString(v_n_1525_, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
v___y_1532_ = v___x_1570_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1571_; 
v_val_1571_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_val_1571_);
lean_dec_ref(v___x_1567_);
v_val_1564_ = v_val_1571_;
goto v___jp_1563_;
}
}
else
{
lean_object* v_val_1572_; 
lean_dec(v_firsts_1529_);
v_val_1572_ = lean_ctor_get(v_____do__lift_1530_, 0);
lean_inc(v_val_1572_);
lean_dec_ref(v_____do__lift_1530_);
v_val_1564_ = v_val_1572_;
goto v___jp_1563_;
}
v___jp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_r_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___y_1532_);
v___x_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1533_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1533_);
v___x_1538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_1539_ = lean_box(2);
v___x_1540_ = 1;
lean_inc_n(v_n_1525_, 3);
v___x_1541_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1525_, v___x_1540_);
v___x_1542_ = lean_string_utf8_byte_size(v___x_1541_);
v___x_1543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1534_);
lean_ctor_set(v___x_1543_, 2, v___x_1542_);
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_n_1525_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v___x_1544_);
v___x_1547_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1539_);
lean_ctor_set(v___x_1547_, 1, v___x_1543_);
lean_ctor_set(v___x_1547_, 2, v_n_1525_);
lean_ctor_set(v___x_1547_, 3, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1538_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_LocalContext_empty;
v___x_1550_ = lean_box(0);
v___x_1551_ = l_Lean_Expr_const___override(v_n_1525_, v___y_1526_);
v___x_1552_ = 0;
v___x_1553_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1553_, 0, v___x_1548_);
lean_ctor_set(v___x_1553_, 1, v___x_1549_);
lean_ctor_set(v___x_1553_, 2, v___x_1550_);
lean_ctor_set(v___x_1553_, 3, v___x_1551_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*4, v___x_1552_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*4 + 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1534_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1544_);
v___x_1557_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v_r_1558_ = lean_box(1);
v___x_1559_ = l_List_forIn_x27_loop___redArg(v___x_1557_, v___f_1527_, v___x_1556_, v_r_1558_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1537_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
v___x_1562_ = lean_apply_2(v_toPure_1528_, lean_box(0), v___x_1561_);
return v___x_1562_;
}
v___jp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_val_1564_);
v___y_1532_ = v___x_1565_;
goto v___jp_1531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3(lean_object* v_n_1573_, lean_object* v___f_1574_, lean_object* v_toPure_1575_, lean_object* v_firsts_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_toBind_1579_, lean_object* v___x_1580_, lean_object* v___x_1581_, lean_object* v___f_1582_, lean_object* v_env_1583_){
_start:
{
lean_object* v___y_1585_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = l_Lean_Environment_constants(v_env_1583_);
lean_inc(v_n_1573_);
v___x_1590_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1580_, v___x_1581_, v___x_1589_, v_n_1573_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1591_; 
lean_dec_ref(v___f_1582_);
v___x_1591_ = lean_box(0);
v___y_1585_ = v___x_1591_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_val_1592_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1592_);
lean_dec_ref(v___x_1590_);
v___x_1593_ = l_Lean_ConstantInfo_levelParams(v_val_1592_);
lean_dec(v_val_1592_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_List_mapTR_loop___redArg(v___f_1582_, v___x_1593_, v___x_1594_);
v___y_1585_ = v___x_1595_;
goto v___jp_1584_;
}
v___jp_1584_:
{
lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_inc(v_n_1573_);
v___f_1586_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1586_, 0, v_n_1573_);
lean_closure_set(v___f_1586_, 1, v___y_1585_);
lean_closure_set(v___f_1586_, 2, v___f_1574_);
lean_closure_set(v___f_1586_, 3, v_toPure_1575_);
lean_closure_set(v___f_1586_, 4, v_firsts_1576_);
v___x_1587_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1577_, v_inst_1578_, v_n_1573_);
v___x_1588_ = lean_apply_4(v_toBind_1579_, lean_box(0), lean_box(0), v___x_1587_, v___f_1586_);
return v___x_1588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_firsts_1602_, lean_object* v_n_1603_){
_start:
{
lean_object* v_toApplicative_1604_; lean_object* v_toBind_1605_; lean_object* v_getEnv_1606_; lean_object* v_toPure_1607_; lean_object* v___f_1608_; lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; 
v_toApplicative_1604_ = lean_ctor_get(v_inst_1600_, 0);
v_toBind_1605_ = lean_ctor_get(v_inst_1600_, 1);
lean_inc_n(v_toBind_1605_, 2);
v_getEnv_1606_ = lean_ctor_get(v_inst_1601_, 0);
lean_inc(v_getEnv_1606_);
v_toPure_1607_ = lean_ctor_get(v_toApplicative_1604_, 1);
lean_inc(v_toPure_1607_);
v___f_1608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1));
v___f_1609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2));
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1611_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1612_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3), 11, 10);
lean_closure_set(v___f_1612_, 0, v_n_1603_);
lean_closure_set(v___f_1612_, 1, v___f_1608_);
lean_closure_set(v___f_1612_, 2, v_toPure_1607_);
lean_closure_set(v___f_1612_, 3, v_firsts_1602_);
lean_closure_set(v___f_1612_, 4, v_inst_1600_);
lean_closure_set(v___f_1612_, 5, v_inst_1601_);
lean_closure_set(v___f_1612_, 6, v_toBind_1605_);
lean_closure_set(v___f_1612_, 7, v___x_1610_);
lean_closure_set(v___f_1612_, 8, v___x_1611_);
lean_closure_set(v___f_1612_, 9, v___f_1609_);
v___x_1613_ = lean_apply_4(v_toBind_1605_, lean_box(0), lean_box(0), v_getEnv_1606_, v___f_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_firsts_1617_, lean_object* v_n_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1615_, v_inst_1616_, v_firsts_1617_, v_n_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1624_);
lean_dec_ref(v_s_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1626_, lean_object* v_x1_1627_, lean_object* v_x2_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1629_ = l_Lean_Name_toString(v_x1_1627_, v___x_1626_);
v___x_1630_ = l_Lean_Name_toString(v_x2_1628_, v___x_1626_);
v___x_1631_ = lean_string_dec_lt(v___x_1629_, v___x_1630_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v___x_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1632_, lean_object* v_x1_1633_, lean_object* v_x2_1634_){
_start:
{
uint8_t v___x_18064__boxed_1635_; uint8_t v_res_1636_; lean_object* v_r_1637_; 
v___x_18064__boxed_1635_ = lean_unbox(v___x_1632_);
v_res_1636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_18064__boxed_1635_, v_x1_1633_, v_x2_1634_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_as_1638_, lean_object* v_lo_1639_, lean_object* v_hi_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_lt(v_lo_1639_, v_hi_1640_);
if (v___x_1641_ == 0)
{
lean_dec(v_lo_1639_);
return v_as_1638_;
}
else
{
lean_object* v___x_1642_; lean_object* v___f_1643_; lean_object* v___x_1644_; lean_object* v_fst_1645_; lean_object* v_snd_1646_; uint8_t v___x_1647_; 
v___x_1642_ = lean_box(v___x_1641_);
v___f_1643_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1643_, 0, v___x_1642_);
lean_inc(v_lo_1639_);
v___x_1644_ = l_Array_qpartition___redArg(v_as_1638_, v___f_1643_, v_lo_1639_, v_hi_1640_);
v_fst_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_fst_1645_);
v_snd_1646_ = lean_ctor_get(v___x_1644_, 1);
lean_inc(v_snd_1646_);
lean_dec_ref(v___x_1644_);
v___x_1647_ = lean_nat_dec_le(v_hi_1640_, v_fst_1645_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_snd_1646_, v_lo_1639_, v_fst_1645_);
v___x_1649_ = lean_unsigned_to_nat(1u);
v___x_1650_ = lean_nat_add(v_fst_1645_, v___x_1649_);
lean_dec(v_fst_1645_);
v_as_1638_ = v___x_1648_;
v_lo_1639_ = v___x_1650_;
goto _start;
}
else
{
lean_dec(v_fst_1645_);
lean_dec(v_lo_1639_);
return v_snd_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_as_1652_, lean_object* v_lo_1653_, lean_object* v_hi_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_as_1652_, v_lo_1653_, v_hi_1654_);
lean_dec(v_hi_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(lean_object* v_a_1656_, lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_box(0);
return v___x_1658_;
}
else
{
lean_object* v_key_1659_; lean_object* v_value_1660_; lean_object* v_tail_1661_; uint8_t v___x_1662_; 
v_key_1659_ = lean_ctor_get(v_x_1657_, 0);
v_value_1660_ = lean_ctor_get(v_x_1657_, 1);
v_tail_1661_ = lean_ctor_get(v_x_1657_, 2);
v___x_1662_ = lean_name_eq(v_key_1659_, v_a_1656_);
if (v___x_1662_ == 0)
{
v_x_1657_ = v_tail_1661_;
goto _start;
}
else
{
lean_object* v___x_1664_; 
lean_inc(v_value_1660_);
v___x_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_value_1660_);
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg___boxed(lean_object* v_a_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1665_, v_x_1666_);
lean_dec(v_x_1666_);
lean_dec(v_a_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(lean_object* v_m_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_buckets_1670_; lean_object* v___x_1671_; uint64_t v___y_1673_; 
v_buckets_1670_ = lean_ctor_get(v_m_1668_, 1);
v___x_1671_ = lean_array_get_size(v_buckets_1670_);
if (lean_obj_tag(v_a_1669_) == 0)
{
uint64_t v___x_1687_; 
v___x_1687_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1673_ = v___x_1687_;
goto v___jp_1672_;
}
else
{
uint64_t v_hash_1688_; 
v_hash_1688_ = lean_ctor_get_uint64(v_a_1669_, sizeof(void*)*2);
v___y_1673_ = v_hash_1688_;
goto v___jp_1672_;
}
v___jp_1672_:
{
uint64_t v___x_1674_; uint64_t v___x_1675_; uint64_t v_fold_1676_; uint64_t v___x_1677_; uint64_t v___x_1678_; uint64_t v___x_1679_; size_t v___x_1680_; size_t v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; size_t v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1674_ = 32ULL;
v___x_1675_ = lean_uint64_shift_right(v___y_1673_, v___x_1674_);
v_fold_1676_ = lean_uint64_xor(v___y_1673_, v___x_1675_);
v___x_1677_ = 16ULL;
v___x_1678_ = lean_uint64_shift_right(v_fold_1676_, v___x_1677_);
v___x_1679_ = lean_uint64_xor(v_fold_1676_, v___x_1678_);
v___x_1680_ = lean_uint64_to_usize(v___x_1679_);
v___x_1681_ = lean_usize_of_nat(v___x_1671_);
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_sub(v___x_1681_, v___x_1682_);
v___x_1684_ = lean_usize_land(v___x_1680_, v___x_1683_);
v___x_1685_ = lean_array_uget_borrowed(v_buckets_1670_, v___x_1684_);
v___x_1686_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1669_, v___x_1685_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg___boxed(lean_object* v_m_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_m_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1692_, lean_object* v_vals_1693_, lean_object* v_i_1694_, lean_object* v_k_1695_){
_start:
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = lean_array_get_size(v_keys_1692_);
v___x_1697_ = lean_nat_dec_lt(v_i_1694_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_dec(v_i_1694_);
v___x_1698_ = lean_box(0);
return v___x_1698_;
}
else
{
lean_object* v_k_x27_1699_; uint8_t v___x_1700_; 
v_k_x27_1699_ = lean_array_fget_borrowed(v_keys_1692_, v_i_1694_);
v___x_1700_ = lean_name_eq(v_k_1695_, v_k_x27_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_unsigned_to_nat(1u);
v___x_1702_ = lean_nat_add(v_i_1694_, v___x_1701_);
lean_dec(v_i_1694_);
v_i_1694_ = v___x_1702_;
goto _start;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_array_fget_borrowed(v_vals_1693_, v_i_1694_);
lean_dec(v_i_1694_);
lean_inc(v___x_1704_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
return v___x_1705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1706_, lean_object* v_vals_1707_, lean_object* v_i_1708_, lean_object* v_k_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1706_, v_vals_1707_, v_i_1708_, v_k_1709_);
lean_dec(v_k_1709_);
lean_dec_ref(v_vals_1707_);
lean_dec_ref(v_keys_1706_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1711_, size_t v_x_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 0)
{
lean_object* v_es_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1735_; 
v_es_1714_ = lean_ctor_get(v_x_1711_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_x_1711_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1716_ = v_x_1711_;
v_isShared_1717_ = v_isSharedCheck_1735_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_es_1714_);
lean_dec(v_x_1711_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1735_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; size_t v___x_1721_; lean_object* v_j_1722_; lean_object* v___x_1723_; 
v___x_1718_ = lean_box(2);
v___x_1719_ = ((size_t)5ULL);
v___x_1720_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1721_ = lean_usize_land(v_x_1712_, v___x_1720_);
v_j_1722_ = lean_usize_to_nat(v___x_1721_);
v___x_1723_ = lean_array_get(v___x_1718_, v_es_1714_, v_j_1722_);
lean_dec(v_j_1722_);
lean_dec_ref(v_es_1714_);
switch(lean_obj_tag(v___x_1723_))
{
case 0:
{
lean_object* v_key_1724_; lean_object* v_val_1725_; uint8_t v___x_1726_; 
v_key_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_key_1724_);
v_val_1725_ = lean_ctor_get(v___x_1723_, 1);
lean_inc(v_val_1725_);
lean_dec_ref(v___x_1723_);
v___x_1726_ = lean_name_eq(v_x_1713_, v_key_1724_);
lean_dec(v_key_1724_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
lean_dec(v_val_1725_);
lean_del_object(v___x_1716_);
v___x_1727_ = lean_box(0);
return v___x_1727_;
}
else
{
lean_object* v___x_1729_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set_tag(v___x_1716_, 1);
lean_ctor_set(v___x_1716_, 0, v_val_1725_);
v___x_1729_ = v___x_1716_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_val_1725_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
case 1:
{
lean_object* v_node_1731_; size_t v___x_1732_; 
lean_del_object(v___x_1716_);
v_node_1731_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_node_1731_);
lean_dec_ref(v___x_1723_);
v___x_1732_ = lean_usize_shift_right(v_x_1712_, v___x_1719_);
v_x_1711_ = v_node_1731_;
v_x_1712_ = v___x_1732_;
goto _start;
}
default: 
{
lean_object* v___x_1734_; 
lean_del_object(v___x_1716_);
v___x_1734_ = lean_box(0);
return v___x_1734_;
}
}
}
}
else
{
lean_object* v_ks_1736_; lean_object* v_vs_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_ks_1736_ = lean_ctor_get(v_x_1711_, 0);
lean_inc_ref(v_ks_1736_);
v_vs_1737_ = lean_ctor_get(v_x_1711_, 1);
lean_inc_ref(v_vs_1737_);
lean_dec_ref(v_x_1711_);
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1736_, v_vs_1737_, v___x_1738_, v_x_1713_);
lean_dec_ref(v_vs_1737_);
lean_dec_ref(v_ks_1736_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
size_t v_x_18181__boxed_1743_; lean_object* v_res_1744_; 
v_x_18181__boxed_1743_ = lean_unbox_usize(v_x_1741_);
lean_dec(v_x_1741_);
v_res_1744_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1740_, v_x_18181__boxed_1743_, v_x_1742_);
lean_dec(v_x_1742_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
uint64_t v___y_1748_; 
if (lean_obj_tag(v_x_1746_) == 0)
{
uint64_t v___x_1751_; 
v___x_1751_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1748_ = v___x_1751_;
goto v___jp_1747_;
}
else
{
uint64_t v_hash_1752_; 
v_hash_1752_ = lean_ctor_get_uint64(v_x_1746_, sizeof(void*)*2);
v___y_1748_ = v_hash_1752_;
goto v___jp_1747_;
}
v___jp_1747_:
{
size_t v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_uint64_to_usize(v___y_1748_);
v___x_1750_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1745_, v___x_1749_, v_x_1746_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1753_, v_x_1754_);
lean_dec(v_x_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
uint8_t v_stage_u2081_1758_; 
v_stage_u2081_1758_ = lean_ctor_get_uint8(v_x_1756_, sizeof(void*)*2);
if (v_stage_u2081_1758_ == 0)
{
lean_object* v_map_u2081_1759_; lean_object* v_map_u2082_1760_; lean_object* v___x_1761_; 
v_map_u2081_1759_ = lean_ctor_get(v_x_1756_, 0);
lean_inc_ref(v_map_u2081_1759_);
v_map_u2082_1760_ = lean_ctor_get(v_x_1756_, 1);
lean_inc_ref(v_map_u2082_1760_);
lean_dec_ref(v_x_1756_);
v___x_1761_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1759_, v_x_1757_);
lean_dec_ref(v_map_u2081_1759_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1760_, v_x_1757_);
return v___x_1762_;
}
else
{
lean_dec_ref(v_map_u2082_1760_);
return v___x_1761_;
}
}
else
{
lean_object* v_map_u2081_1763_; lean_object* v___x_1764_; 
v_map_u2081_1763_ = lean_ctor_get(v_x_1756_, 0);
lean_inc_ref(v_map_u2081_1763_);
lean_dec_ref(v_x_1756_);
v___x_1764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1763_, v_x_1757_);
lean_dec_ref(v_map_u2081_1763_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg___boxed(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_1765_, v_x_1766_);
lean_dec(v_x_1766_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
if (lean_obj_tag(v_a_1768_) == 0)
{
lean_object* v___x_1770_; 
v___x_1770_ = l_List_reverse___redArg(v_a_1769_);
return v___x_1770_;
}
else
{
lean_object* v_head_1771_; lean_object* v_tail_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1781_; 
v_head_1771_ = lean_ctor_get(v_a_1768_, 0);
v_tail_1772_ = lean_ctor_get(v_a_1768_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_a_1768_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1774_ = v_a_1768_;
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_tail_1772_);
lean_inc(v_head_1771_);
lean_dec(v_a_1768_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = l_Lean_Level_param___override(v_head_1771_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_a_1769_);
lean_ctor_set(v___x_1774_, 0, v___x_1776_);
v___x_1778_ = v___x_1774_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_a_1769_);
v___x_1778_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
v_a_1768_ = v_tail_1772_;
v_a_1769_ = v___x_1778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(lean_object* v_t_1782_, lean_object* v_k_1783_){
_start:
{
if (lean_obj_tag(v_t_1782_) == 0)
{
lean_object* v_k_1784_; lean_object* v_v_1785_; lean_object* v_l_1786_; lean_object* v_r_1787_; uint8_t v___x_1788_; 
v_k_1784_ = lean_ctor_get(v_t_1782_, 1);
v_v_1785_ = lean_ctor_get(v_t_1782_, 2);
v_l_1786_ = lean_ctor_get(v_t_1782_, 3);
v_r_1787_ = lean_ctor_get(v_t_1782_, 4);
v___x_1788_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1783_, v_k_1784_);
switch(v___x_1788_)
{
case 0:
{
v_t_1782_ = v_l_1786_;
goto _start;
}
case 1:
{
lean_object* v___x_1790_; 
lean_inc(v_v_1785_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_v_1785_);
return v___x_1790_;
}
default: 
{
v_t_1782_ = v_r_1787_;
goto _start;
}
}
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_box(0);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg___boxed(lean_object* v_t_1793_, lean_object* v_k_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_1793_, v_k_1794_);
lean_dec(v_k_1794_);
lean_dec(v_t_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1796_, lean_object* v_x2_1797_){
_start:
{
lean_object* v_fst_1798_; lean_object* v_fst_1799_; uint8_t v___x_1800_; 
v_fst_1798_ = lean_ctor_get(v_x1_1796_, 0);
v_fst_1799_ = lean_ctor_get(v_x2_1797_, 0);
v___x_1800_ = l_Lean_Name_quickLt(v_fst_1798_, v_fst_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1801_, lean_object* v_x2_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1801_, v_x2_1802_);
lean_dec_ref(v_x2_1802_);
lean_dec_ref(v_x1_1801_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1805_, lean_object* v_k_1806_, lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v_m_1811_; lean_object* v_a_1812_; uint8_t v___x_1813_; 
v___x_1809_ = lean_nat_add(v_x_1807_, v_x_1808_);
v___x_1810_ = lean_unsigned_to_nat(1u);
v_m_1811_ = lean_nat_shiftr(v___x_1809_, v___x_1810_);
lean_dec(v___x_1809_);
v_a_1812_ = lean_array_fget_borrowed(v_as_1805_, v_m_1811_);
v___x_1813_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1812_, v_k_1806_);
if (v___x_1813_ == 0)
{
uint8_t v___x_1814_; 
lean_dec(v_x_1808_);
v___x_1814_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1806_, v_a_1812_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_dec(v_m_1811_);
lean_dec(v_x_1807_);
lean_inc(v_a_1812_);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_a_1812_);
return v___x_1815_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_nat_dec_eq(v_m_1811_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_nat_sub(v_m_1811_, v___x_1810_);
lean_dec(v_m_1811_);
v___x_1819_ = lean_nat_dec_lt(v___x_1818_, v_x_1807_);
if (v___x_1819_ == 0)
{
v_x_1808_ = v___x_1818_;
goto _start;
}
else
{
lean_object* v___x_1821_; 
lean_dec(v___x_1818_);
lean_dec(v_x_1807_);
v___x_1821_ = lean_box(0);
return v___x_1821_;
}
}
else
{
lean_object* v___x_1822_; 
lean_dec(v_m_1811_);
lean_dec(v_x_1807_);
v___x_1822_ = lean_box(0);
return v___x_1822_;
}
}
}
else
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
lean_dec(v_x_1807_);
v___x_1823_ = lean_nat_add(v_m_1811_, v___x_1810_);
lean_dec(v_m_1811_);
v___x_1824_ = lean_nat_dec_le(v___x_1823_, v_x_1808_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
lean_dec(v___x_1823_);
lean_dec(v_x_1808_);
v___x_1825_ = lean_box(0);
return v___x_1825_;
}
else
{
v_x_1807_ = v___x_1823_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1827_, lean_object* v_k_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1827_, v_k_1828_, v_x_1829_, v_x_1830_);
lean_dec_ref(v_k_1828_);
lean_dec_ref(v_as_1827_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; lean_object* v_env_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1836_ = lean_st_ref_get(v___y_1834_);
v_env_1840_ = lean_ctor_get(v___x_1836_, 0);
lean_inc_ref(v_env_1840_);
lean_dec(v___x_1836_);
v___x_1841_ = lean_box(1);
v___x_1842_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1840_, v_tac_1833_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; lean_object* v_toEnvExtension_1844_; lean_object* v_asyncMode_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1843_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1844_ = lean_ctor_get(v___x_1843_, 0);
v_asyncMode_1845_ = lean_ctor_get(v_toEnvExtension_1844_, 2);
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1841_, v___x_1843_, v_env_1840_, v_asyncMode_1845_, v___x_1846_);
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1847_, v_tac_1833_);
lean_dec(v_tac_1833_);
lean_dec(v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
else
{
lean_object* v_val_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1878_; 
v_val_1850_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1852_ = v___x_1842_;
v_isShared_1853_ = v_isSharedCheck_1878_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_val_1850_);
lean_dec(v___x_1842_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1878_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; uint8_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1854_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1855_ = 0;
v___x_1856_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1841_, v___x_1854_, v_env_1840_, v_val_1850_, v___x_1855_);
lean_dec(v_val_1850_);
lean_dec_ref(v_env_1840_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_array_get_size(v___x_1856_);
v___x_1859_ = lean_nat_dec_lt(v___x_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_dec_ref(v___x_1856_);
lean_del_object(v___x_1852_);
lean_dec(v_tac_1833_);
goto v___jp_1837_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = lean_nat_sub(v___x_1858_, v___x_1860_);
v___x_1862_ = lean_nat_dec_le(v___x_1857_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec(v___x_1861_);
lean_dec_ref(v___x_1856_);
lean_del_object(v___x_1852_);
lean_dec(v_tac_1833_);
goto v___jp_1837_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_tac_1833_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1856_, v___x_1864_, v___x_1857_, v___x_1861_);
lean_dec_ref(v___x_1864_);
lean_dec_ref(v___x_1856_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_del_object(v___x_1852_);
goto v___jp_1837_;
}
else
{
lean_object* v_val_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1877_; 
v_val_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1877_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_val_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1877_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_snd_1870_; lean_object* v___x_1872_; 
v_snd_1870_ = lean_ctor_get(v_val_1866_, 1);
lean_inc(v_snd_1870_);
lean_dec(v_val_1866_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v_snd_1870_);
v___x_1872_ = v___x_1868_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_snd_1870_);
v___x_1872_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1874_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1872_);
v___x_1874_ = v___x_1852_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
}
}
v___jp_1837_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1879_, v___y_1880_);
lean_dec(v___y_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_k_1883_, lean_object* v_v_1884_, lean_object* v_t_1885_){
_start:
{
if (lean_obj_tag(v_t_1885_) == 0)
{
lean_object* v_size_1886_; lean_object* v_k_1887_; lean_object* v_v_1888_; lean_object* v_l_1889_; lean_object* v_r_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_2171_; 
v_size_1886_ = lean_ctor_get(v_t_1885_, 0);
v_k_1887_ = lean_ctor_get(v_t_1885_, 1);
v_v_1888_ = lean_ctor_get(v_t_1885_, 2);
v_l_1889_ = lean_ctor_get(v_t_1885_, 3);
v_r_1890_ = lean_ctor_get(v_t_1885_, 4);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_t_1885_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_1892_ = v_t_1885_;
v_isShared_1893_ = v_isSharedCheck_2171_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_r_1890_);
lean_inc(v_l_1889_);
lean_inc(v_v_1888_);
lean_inc(v_k_1887_);
lean_inc(v_size_1886_);
lean_dec(v_t_1885_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_2171_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_lt(v_k_1883_, v_k_1887_);
if (v___x_1894_ == 0)
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_nat_dec_eq(v_k_1883_, v_k_1887_);
if (v___x_1895_ == 0)
{
lean_object* v_impl_1896_; lean_object* v___x_1897_; 
lean_dec(v_size_1886_);
v_impl_1896_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1883_, v_v_1884_, v_r_1890_);
v___x_1897_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1889_) == 0)
{
lean_object* v_size_1898_; lean_object* v_size_1899_; lean_object* v_k_1900_; lean_object* v_v_1901_; lean_object* v_l_1902_; lean_object* v_r_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v_size_1898_ = lean_ctor_get(v_l_1889_, 0);
v_size_1899_ = lean_ctor_get(v_impl_1896_, 0);
lean_inc(v_size_1899_);
v_k_1900_ = lean_ctor_get(v_impl_1896_, 1);
lean_inc(v_k_1900_);
v_v_1901_ = lean_ctor_get(v_impl_1896_, 2);
lean_inc(v_v_1901_);
v_l_1902_ = lean_ctor_get(v_impl_1896_, 3);
lean_inc(v_l_1902_);
v_r_1903_ = lean_ctor_get(v_impl_1896_, 4);
lean_inc(v_r_1903_);
v___x_1904_ = lean_unsigned_to_nat(3u);
v___x_1905_ = lean_nat_mul(v___x_1904_, v_size_1898_);
v___x_1906_ = lean_nat_dec_lt(v___x_1905_, v_size_1899_);
lean_dec(v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_dec(v_r_1903_);
lean_dec(v_l_1902_);
lean_dec(v_v_1901_);
lean_dec(v_k_1900_);
v___x_1907_ = lean_nat_add(v___x_1897_, v_size_1898_);
v___x_1908_ = lean_nat_add(v___x_1907_, v_size_1899_);
lean_dec(v_size_1899_);
lean_dec(v___x_1907_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v_impl_1896_);
lean_ctor_set(v___x_1892_, 0, v___x_1908_);
v___x_1910_ = v___x_1892_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_1911_, 3, v_l_1889_);
lean_ctor_set(v_reuseFailAlloc_1911_, 4, v_impl_1896_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
else
{
lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1975_; 
v_isSharedCheck_1975_ = !lean_is_exclusive(v_impl_1896_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; lean_object* v_unused_1977_; lean_object* v_unused_1978_; lean_object* v_unused_1979_; lean_object* v_unused_1980_; 
v_unused_1976_ = lean_ctor_get(v_impl_1896_, 4);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_impl_1896_, 3);
lean_dec(v_unused_1977_);
v_unused_1978_ = lean_ctor_get(v_impl_1896_, 2);
lean_dec(v_unused_1978_);
v_unused_1979_ = lean_ctor_get(v_impl_1896_, 1);
lean_dec(v_unused_1979_);
v_unused_1980_ = lean_ctor_get(v_impl_1896_, 0);
lean_dec(v_unused_1980_);
v___x_1913_ = v_impl_1896_;
v_isShared_1914_ = v_isSharedCheck_1975_;
goto v_resetjp_1912_;
}
else
{
lean_dec(v_impl_1896_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1975_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_size_1915_; lean_object* v_k_1916_; lean_object* v_v_1917_; lean_object* v_l_1918_; lean_object* v_r_1919_; lean_object* v_size_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v_size_1915_ = lean_ctor_get(v_l_1902_, 0);
v_k_1916_ = lean_ctor_get(v_l_1902_, 1);
v_v_1917_ = lean_ctor_get(v_l_1902_, 2);
v_l_1918_ = lean_ctor_get(v_l_1902_, 3);
v_r_1919_ = lean_ctor_get(v_l_1902_, 4);
v_size_1920_ = lean_ctor_get(v_r_1903_, 0);
v___x_1921_ = lean_unsigned_to_nat(2u);
v___x_1922_ = lean_nat_mul(v___x_1921_, v_size_1920_);
v___x_1923_ = lean_nat_dec_lt(v_size_1915_, v___x_1922_);
lean_dec(v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1951_; 
lean_inc(v_r_1919_);
lean_inc(v_l_1918_);
lean_inc(v_v_1917_);
lean_inc(v_k_1916_);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_l_1902_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; lean_object* v_unused_1953_; lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; 
v_unused_1952_ = lean_ctor_get(v_l_1902_, 4);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_l_1902_, 3);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_l_1902_, 2);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_l_1902_, 1);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_l_1902_, 0);
lean_dec(v_unused_1956_);
v___x_1925_ = v_l_1902_;
v_isShared_1926_ = v_isSharedCheck_1951_;
goto v_resetjp_1924_;
}
else
{
lean_dec(v_l_1902_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1951_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1941_; 
v___x_1927_ = lean_nat_add(v___x_1897_, v_size_1898_);
v___x_1928_ = lean_nat_add(v___x_1927_, v_size_1899_);
lean_dec(v_size_1899_);
if (lean_obj_tag(v_l_1918_) == 0)
{
lean_object* v_size_1949_; 
v_size_1949_ = lean_ctor_get(v_l_1918_, 0);
lean_inc(v_size_1949_);
v___y_1941_ = v_size_1949_;
goto v___jp_1940_;
}
else
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_unsigned_to_nat(0u);
v___y_1941_ = v___x_1950_;
goto v___jp_1940_;
}
v___jp_1929_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = lean_nat_add(v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 4, v_r_1903_);
lean_ctor_set(v___x_1925_, 3, v_r_1919_);
lean_ctor_set(v___x_1925_, 2, v_v_1901_);
lean_ctor_set(v___x_1925_, 1, v_k_1900_);
lean_ctor_set(v___x_1925_, 0, v___x_1933_);
v___x_1935_ = v___x_1925_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_k_1900_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_v_1901_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_r_1919_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_r_1903_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 4, v___x_1935_);
lean_ctor_set(v___x_1913_, 3, v___y_1930_);
lean_ctor_set(v___x_1913_, 2, v_v_1917_);
lean_ctor_set(v___x_1913_, 1, v_k_1916_);
lean_ctor_set(v___x_1913_, 0, v___x_1928_);
v___x_1937_ = v___x_1913_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_k_1916_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_v_1917_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v___y_1930_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
v___jp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_nat_add(v___x_1927_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec(v___x_1927_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v_l_1918_);
lean_ctor_set(v___x_1892_, 0, v___x_1942_);
v___x_1944_ = v___x_1892_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_l_1889_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_l_1918_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_nat_add(v___x_1897_, v_size_1920_);
if (lean_obj_tag(v_r_1919_) == 0)
{
lean_object* v_size_1946_; 
v_size_1946_ = lean_ctor_get(v_r_1919_, 0);
lean_inc(v_size_1946_);
v___y_1930_ = v___x_1944_;
v___y_1931_ = v___x_1945_;
v___y_1932_ = v_size_1946_;
goto v___jp_1929_;
}
else
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_unsigned_to_nat(0u);
v___y_1930_ = v___x_1944_;
v___y_1931_ = v___x_1945_;
v___y_1932_ = v___x_1947_;
goto v___jp_1929_;
}
}
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
lean_del_object(v___x_1892_);
v___x_1957_ = lean_nat_add(v___x_1897_, v_size_1898_);
v___x_1958_ = lean_nat_add(v___x_1957_, v_size_1899_);
lean_dec(v_size_1899_);
v___x_1959_ = lean_nat_add(v___x_1957_, v_size_1915_);
lean_dec(v___x_1957_);
lean_inc_ref(v_l_1889_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 4, v_l_1902_);
lean_ctor_set(v___x_1913_, 3, v_l_1889_);
lean_ctor_set(v___x_1913_, 2, v_v_1888_);
lean_ctor_set(v___x_1913_, 1, v_k_1887_);
lean_ctor_set(v___x_1913_, 0, v___x_1959_);
v___x_1961_ = v___x_1913_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_l_1889_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v_l_1902_);
v___x_1961_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
v_isSharedCheck_1968_ = !lean_is_exclusive(v_l_1889_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; lean_object* v_unused_1972_; lean_object* v_unused_1973_; 
v_unused_1969_ = lean_ctor_get(v_l_1889_, 4);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_l_1889_, 3);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_l_1889_, 2);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_l_1889_, 1);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v_l_1889_, 0);
lean_dec(v_unused_1973_);
v___x_1963_ = v_l_1889_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v_l_1889_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 4, v_r_1903_);
lean_ctor_set(v___x_1963_, 3, v___x_1961_);
lean_ctor_set(v___x_1963_, 2, v_v_1901_);
lean_ctor_set(v___x_1963_, 1, v_k_1900_);
lean_ctor_set(v___x_1963_, 0, v___x_1958_);
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_k_1900_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_v_1901_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_r_1903_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1981_; 
v_l_1981_ = lean_ctor_get(v_impl_1896_, 3);
lean_inc(v_l_1981_);
if (lean_obj_tag(v_l_1981_) == 0)
{
lean_object* v_r_1982_; lean_object* v_k_1983_; lean_object* v_v_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2007_; 
v_r_1982_ = lean_ctor_get(v_impl_1896_, 4);
v_k_1983_ = lean_ctor_get(v_impl_1896_, 1);
v_v_1984_ = lean_ctor_get(v_impl_1896_, 2);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_impl_1896_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; lean_object* v_unused_2009_; 
v_unused_2008_ = lean_ctor_get(v_impl_1896_, 3);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_impl_1896_, 0);
lean_dec(v_unused_2009_);
v___x_1986_ = v_impl_1896_;
v_isShared_1987_ = v_isSharedCheck_2007_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_r_1982_);
lean_inc(v_v_1984_);
lean_inc(v_k_1983_);
lean_dec(v_impl_1896_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2007_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_k_1988_; lean_object* v_v_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2003_; 
v_k_1988_ = lean_ctor_get(v_l_1981_, 1);
v_v_1989_ = lean_ctor_get(v_l_1981_, 2);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_l_1981_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; lean_object* v_unused_2005_; lean_object* v_unused_2006_; 
v_unused_2004_ = lean_ctor_get(v_l_1981_, 4);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_l_1981_, 3);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_l_1981_, 0);
lean_dec(v_unused_2006_);
v___x_1991_ = v_l_1981_;
v_isShared_1992_ = v_isSharedCheck_2003_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_v_1989_);
lean_inc(v_k_1988_);
lean_dec(v_l_1981_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2003_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1982_, 2);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v_r_1982_);
lean_ctor_set(v___x_1991_, 3, v_r_1982_);
lean_ctor_set(v___x_1991_, 2, v_v_1888_);
lean_ctor_set(v___x_1991_, 1, v_k_1887_);
lean_ctor_set(v___x_1991_, 0, v___x_1897_);
v___x_1995_ = v___x_1991_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_r_1982_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v_r_1982_);
v___x_1995_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
lean_inc(v_r_1982_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 3, v_r_1982_);
lean_ctor_set(v___x_1986_, 0, v___x_1897_);
v___x_1997_ = v___x_1986_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_r_1982_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_r_1982_);
v___x_1997_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1999_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v___x_1997_);
lean_ctor_set(v___x_1892_, 3, v___x_1995_);
lean_ctor_set(v___x_1892_, 2, v_v_1989_);
lean_ctor_set(v___x_1892_, 1, v_k_1988_);
lean_ctor_set(v___x_1892_, 0, v___x_1993_);
v___x_1999_ = v___x_1892_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_k_1988_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_v_1989_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
}
else
{
lean_object* v_r_2010_; 
v_r_2010_ = lean_ctor_get(v_impl_1896_, 4);
lean_inc(v_r_2010_);
if (lean_obj_tag(v_r_2010_) == 0)
{
lean_object* v_k_2011_; lean_object* v_v_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2023_; 
v_k_2011_ = lean_ctor_get(v_impl_1896_, 1);
v_v_2012_ = lean_ctor_get(v_impl_1896_, 2);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_impl_1896_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; lean_object* v_unused_2025_; lean_object* v_unused_2026_; 
v_unused_2024_ = lean_ctor_get(v_impl_1896_, 4);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_impl_1896_, 3);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_impl_1896_, 0);
lean_dec(v_unused_2026_);
v___x_2014_ = v_impl_1896_;
v_isShared_2015_ = v_isSharedCheck_2023_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_v_2012_);
lean_inc(v_k_2011_);
lean_dec(v_impl_1896_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2023_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_unsigned_to_nat(3u);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 4, v_l_1981_);
lean_ctor_set(v___x_2014_, 2, v_v_1888_);
lean_ctor_set(v___x_2014_, 1, v_k_1887_);
lean_ctor_set(v___x_2014_, 0, v___x_1897_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_l_1981_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_l_1981_);
v___x_2018_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v_r_2010_);
lean_ctor_set(v___x_1892_, 3, v___x_2018_);
lean_ctor_set(v___x_1892_, 2, v_v_2012_);
lean_ctor_set(v___x_1892_, 1, v_k_2011_);
lean_ctor_set(v___x_1892_, 0, v___x_2016_);
v___x_2020_ = v___x_1892_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_k_2011_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_v_2012_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v_r_2010_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_unsigned_to_nat(2u);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v_impl_1896_);
lean_ctor_set(v___x_1892_, 3, v_r_2010_);
lean_ctor_set(v___x_1892_, 0, v___x_2027_);
v___x_2029_ = v___x_1892_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2030_, 3, v_r_2010_);
lean_ctor_set(v_reuseFailAlloc_2030_, 4, v_impl_1896_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v___x_2032_; 
lean_dec(v_v_1888_);
lean_dec(v_k_1887_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 2, v_v_1884_);
lean_ctor_set(v___x_1892_, 1, v_k_1883_);
v___x_2032_ = v___x_1892_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_size_1886_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_1883_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_1884_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v_l_1889_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v_r_1890_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
else
{
lean_object* v_impl_2034_; lean_object* v___x_2035_; 
lean_dec(v_size_1886_);
v_impl_2034_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1883_, v_v_1884_, v_l_1889_);
v___x_2035_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1890_) == 0)
{
lean_object* v_size_2036_; lean_object* v_size_2037_; lean_object* v_k_2038_; lean_object* v_v_2039_; lean_object* v_l_2040_; lean_object* v_r_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_size_2036_ = lean_ctor_get(v_r_1890_, 0);
v_size_2037_ = lean_ctor_get(v_impl_2034_, 0);
lean_inc(v_size_2037_);
v_k_2038_ = lean_ctor_get(v_impl_2034_, 1);
lean_inc(v_k_2038_);
v_v_2039_ = lean_ctor_get(v_impl_2034_, 2);
lean_inc(v_v_2039_);
v_l_2040_ = lean_ctor_get(v_impl_2034_, 3);
lean_inc(v_l_2040_);
v_r_2041_ = lean_ctor_get(v_impl_2034_, 4);
lean_inc(v_r_2041_);
v___x_2042_ = lean_unsigned_to_nat(3u);
v___x_2043_ = lean_nat_mul(v___x_2042_, v_size_2036_);
v___x_2044_ = lean_nat_dec_lt(v___x_2043_, v_size_2037_);
lean_dec(v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec(v_r_2041_);
lean_dec(v_l_2040_);
lean_dec(v_v_2039_);
lean_dec(v_k_2038_);
v___x_2045_ = lean_nat_add(v___x_2035_, v_size_2037_);
lean_dec(v_size_2037_);
v___x_2046_ = lean_nat_add(v___x_2045_, v_size_2036_);
lean_dec(v___x_2045_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 3, v_impl_2034_);
lean_ctor_set(v___x_1892_, 0, v___x_2046_);
v___x_2048_ = v___x_1892_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_impl_2034_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_r_1890_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
else
{
lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2115_; 
v_isSharedCheck_2115_ = !lean_is_exclusive(v_impl_2034_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; lean_object* v_unused_2117_; lean_object* v_unused_2118_; lean_object* v_unused_2119_; lean_object* v_unused_2120_; 
v_unused_2116_ = lean_ctor_get(v_impl_2034_, 4);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_impl_2034_, 3);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_impl_2034_, 2);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_impl_2034_, 1);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_impl_2034_, 0);
lean_dec(v_unused_2120_);
v___x_2051_ = v_impl_2034_;
v_isShared_2052_ = v_isSharedCheck_2115_;
goto v_resetjp_2050_;
}
else
{
lean_dec(v_impl_2034_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2115_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_size_2053_; lean_object* v_size_2054_; lean_object* v_k_2055_; lean_object* v_v_2056_; lean_object* v_l_2057_; lean_object* v_r_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_size_2053_ = lean_ctor_get(v_l_2040_, 0);
v_size_2054_ = lean_ctor_get(v_r_2041_, 0);
v_k_2055_ = lean_ctor_get(v_r_2041_, 1);
v_v_2056_ = lean_ctor_get(v_r_2041_, 2);
v_l_2057_ = lean_ctor_get(v_r_2041_, 3);
v_r_2058_ = lean_ctor_get(v_r_2041_, 4);
v___x_2059_ = lean_unsigned_to_nat(2u);
v___x_2060_ = lean_nat_mul(v___x_2059_, v_size_2053_);
v___x_2061_ = lean_nat_dec_lt(v_size_2054_, v___x_2060_);
lean_dec(v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2090_; 
lean_inc(v_r_2058_);
lean_inc(v_l_2057_);
lean_inc(v_v_2056_);
lean_inc(v_k_2055_);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_r_2041_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; lean_object* v_unused_2095_; 
v_unused_2091_ = lean_ctor_get(v_r_2041_, 4);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_r_2041_, 3);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_r_2041_, 2);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_r_2041_, 1);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_r_2041_, 0);
lean_dec(v_unused_2095_);
v___x_2063_ = v_r_2041_;
v_isShared_2064_ = v_isSharedCheck_2090_;
goto v_resetjp_2062_;
}
else
{
lean_dec(v_r_2041_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2090_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___x_2078_; lean_object* v___y_2080_; 
v___x_2065_ = lean_nat_add(v___x_2035_, v_size_2037_);
lean_dec(v_size_2037_);
v___x_2066_ = lean_nat_add(v___x_2065_, v_size_2036_);
lean_dec(v___x_2065_);
v___x_2078_ = lean_nat_add(v___x_2035_, v_size_2053_);
if (lean_obj_tag(v_l_2057_) == 0)
{
lean_object* v_size_2088_; 
v_size_2088_ = lean_ctor_get(v_l_2057_, 0);
lean_inc(v_size_2088_);
v___y_2080_ = v_size_2088_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v___y_2080_ = v___x_2089_;
goto v___jp_2079_;
}
v___jp_2067_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_nat_add(v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec(v___y_2069_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 4, v_r_1890_);
lean_ctor_set(v___x_2063_, 3, v_r_2058_);
lean_ctor_set(v___x_2063_, 2, v_v_1888_);
lean_ctor_set(v___x_2063_, 1, v_k_1887_);
lean_ctor_set(v___x_2063_, 0, v___x_2071_);
v___x_2073_ = v___x_2063_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_r_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_r_1890_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 4, v___x_2073_);
lean_ctor_set(v___x_2051_, 3, v___y_2068_);
lean_ctor_set(v___x_2051_, 2, v_v_2056_);
lean_ctor_set(v___x_2051_, 1, v_k_2055_);
lean_ctor_set(v___x_2051_, 0, v___x_2066_);
v___x_2075_ = v___x_2051_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_2055_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_2056_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v___y_2068_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
v___jp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_nat_add(v___x_2078_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec(v___x_2078_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v_l_2057_);
lean_ctor_set(v___x_1892_, 3, v_l_2040_);
lean_ctor_set(v___x_1892_, 2, v_v_2039_);
lean_ctor_set(v___x_1892_, 1, v_k_2038_);
lean_ctor_set(v___x_1892_, 0, v___x_2081_);
v___x_2083_ = v___x_1892_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_l_2040_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_l_2057_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_nat_add(v___x_2035_, v_size_2036_);
if (lean_obj_tag(v_r_2058_) == 0)
{
lean_object* v_size_2085_; 
v_size_2085_ = lean_ctor_get(v_r_2058_, 0);
lean_inc(v_size_2085_);
v___y_2068_ = v___x_2083_;
v___y_2069_ = v___x_2084_;
v___y_2070_ = v_size_2085_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v___y_2068_ = v___x_2083_;
v___y_2069_ = v___x_2084_;
v___y_2070_ = v___x_2086_;
goto v___jp_2067_;
}
}
}
}
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_del_object(v___x_1892_);
v___x_2096_ = lean_nat_add(v___x_2035_, v_size_2037_);
lean_dec(v_size_2037_);
v___x_2097_ = lean_nat_add(v___x_2096_, v_size_2036_);
lean_dec(v___x_2096_);
v___x_2098_ = lean_nat_add(v___x_2035_, v_size_2036_);
v___x_2099_ = lean_nat_add(v___x_2098_, v_size_2054_);
lean_dec(v___x_2098_);
lean_inc_ref(v_r_1890_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 4, v_r_1890_);
lean_ctor_set(v___x_2051_, 3, v_r_2041_);
lean_ctor_set(v___x_2051_, 2, v_v_1888_);
lean_ctor_set(v___x_2051_, 1, v_k_1887_);
lean_ctor_set(v___x_2051_, 0, v___x_2099_);
v___x_2101_ = v___x_2051_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_r_1890_);
v___x_2101_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
v_isSharedCheck_2108_ = !lean_is_exclusive(v_r_1890_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; lean_object* v_unused_2110_; lean_object* v_unused_2111_; lean_object* v_unused_2112_; lean_object* v_unused_2113_; 
v_unused_2109_ = lean_ctor_get(v_r_1890_, 4);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_r_1890_, 3);
lean_dec(v_unused_2110_);
v_unused_2111_ = lean_ctor_get(v_r_1890_, 2);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_r_1890_, 1);
lean_dec(v_unused_2112_);
v_unused_2113_ = lean_ctor_get(v_r_1890_, 0);
lean_dec(v_unused_2113_);
v___x_2103_ = v_r_1890_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v_r_1890_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v___x_2101_);
lean_ctor_set(v___x_2103_, 3, v_l_2040_);
lean_ctor_set(v___x_2103_, 2, v_v_2039_);
lean_ctor_set(v___x_2103_, 1, v_k_2038_);
lean_ctor_set(v___x_2103_, 0, v___x_2097_);
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_l_2040_);
lean_ctor_set(v_reuseFailAlloc_2107_, 4, v___x_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2121_; 
v_l_2121_ = lean_ctor_get(v_impl_2034_, 3);
lean_inc(v_l_2121_);
if (lean_obj_tag(v_l_2121_) == 0)
{
lean_object* v_r_2122_; lean_object* v_k_2123_; lean_object* v_v_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2135_; 
v_r_2122_ = lean_ctor_get(v_impl_2034_, 4);
v_k_2123_ = lean_ctor_get(v_impl_2034_, 1);
v_v_2124_ = lean_ctor_get(v_impl_2034_, 2);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_impl_2034_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; lean_object* v_unused_2137_; 
v_unused_2136_ = lean_ctor_get(v_impl_2034_, 3);
lean_dec(v_unused_2136_);
v_unused_2137_ = lean_ctor_get(v_impl_2034_, 0);
lean_dec(v_unused_2137_);
v___x_2126_ = v_impl_2034_;
v_isShared_2127_ = v_isSharedCheck_2135_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_r_2122_);
lean_inc(v_v_2124_);
lean_inc(v_k_2123_);
lean_dec(v_impl_2034_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2135_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2122_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 3, v_r_2122_);
lean_ctor_set(v___x_2126_, 2, v_v_1888_);
lean_ctor_set(v___x_2126_, 1, v_k_1887_);
lean_ctor_set(v___x_2126_, 0, v___x_2035_);
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_r_2122_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_r_2122_);
v___x_2130_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2132_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v___x_2130_);
lean_ctor_set(v___x_1892_, 3, v_l_2121_);
lean_ctor_set(v___x_1892_, 2, v_v_2124_);
lean_ctor_set(v___x_1892_, 1, v_k_2123_);
lean_ctor_set(v___x_1892_, 0, v___x_2128_);
v___x_2132_ = v___x_1892_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_k_2123_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_v_2124_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_l_2121_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_r_2138_; 
v_r_2138_ = lean_ctor_get(v_impl_2034_, 4);
lean_inc(v_r_2138_);
if (lean_obj_tag(v_r_2138_) == 0)
{
lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2163_; 
v_k_2139_ = lean_ctor_get(v_impl_2034_, 1);
v_v_2140_ = lean_ctor_get(v_impl_2034_, 2);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_impl_2034_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; lean_object* v_unused_2165_; lean_object* v_unused_2166_; 
v_unused_2164_ = lean_ctor_get(v_impl_2034_, 4);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_impl_2034_, 3);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_impl_2034_, 0);
lean_dec(v_unused_2166_);
v___x_2142_ = v_impl_2034_;
v_isShared_2143_ = v_isSharedCheck_2163_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_v_2140_);
lean_inc(v_k_2139_);
lean_dec(v_impl_2034_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2163_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_k_2144_; lean_object* v_v_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2159_; 
v_k_2144_ = lean_ctor_get(v_r_2138_, 1);
v_v_2145_ = lean_ctor_get(v_r_2138_, 2);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_r_2138_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2160_ = lean_ctor_get(v_r_2138_, 4);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_r_2138_, 3);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_r_2138_, 0);
lean_dec(v_unused_2162_);
v___x_2147_ = v_r_2138_;
v_isShared_2148_ = v_isSharedCheck_2159_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_v_2145_);
lean_inc(v_k_2144_);
lean_dec(v_r_2138_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2159_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_unsigned_to_nat(3u);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 4, v_l_2121_);
lean_ctor_set(v___x_2147_, 3, v_l_2121_);
lean_ctor_set(v___x_2147_, 2, v_v_2140_);
lean_ctor_set(v___x_2147_, 1, v_k_2139_);
lean_ctor_set(v___x_2147_, 0, v___x_2035_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_l_2121_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_l_2121_);
v___x_2151_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 4, v_l_2121_);
lean_ctor_set(v___x_2142_, 2, v_v_1888_);
lean_ctor_set(v___x_2142_, 1, v_k_1887_);
lean_ctor_set(v___x_2142_, 0, v___x_2035_);
v___x_2153_ = v___x_2142_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_l_2121_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_l_2121_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v___x_2153_);
lean_ctor_set(v___x_1892_, 3, v___x_2151_);
lean_ctor_set(v___x_1892_, 2, v_v_2145_);
lean_ctor_set(v___x_1892_, 1, v_k_2144_);
lean_ctor_set(v___x_1892_, 0, v___x_2149_);
v___x_2155_ = v___x_1892_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_2144_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_2145_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = lean_unsigned_to_nat(2u);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v_r_2138_);
lean_ctor_set(v___x_1892_, 3, v_impl_2034_);
lean_ctor_set(v___x_1892_, 0, v___x_2167_);
v___x_2169_ = v___x_1892_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_k_1887_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_v_1888_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_impl_2034_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_r_2138_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v_k_1883_);
lean_ctor_set(v___x_2173_, 2, v_v_1884_);
lean_ctor_set(v___x_2173_, 3, v_t_1885_);
lean_ctor_set(v___x_2173_, 4, v_t_1885_);
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_as_x27_2174_, lean_object* v_b_2175_){
_start:
{
if (lean_obj_tag(v_as_x27_2174_) == 0)
{
return v_b_2175_;
}
else
{
lean_object* v_head_2176_; lean_object* v_tail_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v_r_2180_; 
v_head_2176_ = lean_ctor_get(v_as_x27_2174_, 0);
lean_inc(v_head_2176_);
v_tail_2177_ = lean_ctor_get(v_as_x27_2174_, 1);
lean_inc(v_tail_2177_);
lean_dec_ref(v_as_x27_2174_);
v_fst_2178_ = lean_ctor_get(v_head_2176_, 0);
lean_inc(v_fst_2178_);
v_snd_2179_ = lean_ctor_get(v_head_2176_, 1);
lean_inc(v_snd_2179_);
lean_dec(v_head_2176_);
v_r_2180_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_fst_2178_, v_snd_2179_, v_b_2175_);
v_as_x27_2174_ = v_tail_2177_;
v_b_2175_ = v_r_2180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_2182_, lean_object* v_n_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2220_; lean_object* v_val_2221_; lean_object* v___x_2223_; lean_object* v___y_2225_; lean_object* v_env_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2223_ = lean_st_ref_get(v___y_2185_);
v_env_2240_ = lean_ctor_get(v___x_2223_, 0);
lean_inc_ref(v_env_2240_);
lean_dec(v___x_2223_);
v___x_2241_ = l_Lean_Environment_constants(v_env_2240_);
v___x_2242_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v___x_2241_, v_n_2183_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_box(0);
v___y_2225_ = v___x_2243_;
goto v___jp_2224_;
}
else
{
lean_object* v_val_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_val_2244_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_val_2244_);
lean_dec_ref(v___x_2242_);
v___x_2245_ = l_Lean_ConstantInfo_levelParams(v_val_2244_);
lean_dec(v_val_2244_);
v___x_2246_ = lean_box(0);
v___x_2247_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(v___x_2245_, v___x_2246_);
v___y_2225_ = v___x_2247_;
goto v___jp_2224_;
}
v___jp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v_r_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___y_2189_);
v___x_2193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2190_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2190_);
v___x_2195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_2196_ = lean_box(2);
v___x_2197_ = 1;
lean_inc_n(v_n_2183_, 3);
v___x_2198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_2183_, v___x_2197_);
v___x_2199_ = lean_string_utf8_byte_size(v___x_2198_);
v___x_2200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2191_);
lean_ctor_set(v___x_2200_, 2, v___x_2199_);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_n_2183_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2201_);
v___x_2204_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2196_);
lean_ctor_set(v___x_2204_, 1, v___x_2200_);
lean_ctor_set(v___x_2204_, 2, v_n_2183_);
lean_ctor_set(v___x_2204_, 3, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2195_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = l_Lean_LocalContext_empty;
v___x_2207_ = lean_box(0);
v___x_2208_ = l_Lean_Expr_const___override(v_n_2183_, v___y_2188_);
v___x_2209_ = 0;
v___x_2210_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2210_, 0, v___x_2205_);
lean_ctor_set(v___x_2210_, 1, v___x_2206_);
lean_ctor_set(v___x_2210_, 2, v___x_2207_);
lean_ctor_set(v___x_2210_, 3, v___x_2208_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*4, v___x_2209_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*4 + 1, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2191_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___x_2201_);
v_r_2214_ = lean_box(1);
v___x_2215_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_2213_, v_r_2214_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2194_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
return v___x_2218_;
}
v___jp_2219_:
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_val_2221_);
v___y_2188_ = v___y_2220_;
v___y_2189_ = v___x_2222_;
goto v___jp_2187_;
}
v___jp_2224_:
{
lean_object* v___x_2226_; lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2239_; 
lean_inc(v_n_2183_);
v___x_2226_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_2183_, v___y_2185_);
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2239_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2239_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
if (lean_obj_tag(v_a_2227_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_firsts_2182_, v_n_2183_);
if (lean_obj_tag(v___x_2231_) == 0)
{
uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2232_ = 1;
lean_inc(v_n_2183_);
v___x_2233_ = l_Lean_Name_toString(v_n_2183_, v___x_2232_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 3);
lean_ctor_set(v___x_2229_, 0, v___x_2233_);
v___x_2235_ = v___x_2229_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
v___y_2188_ = v___y_2225_;
v___y_2189_ = v___x_2235_;
goto v___jp_2187_;
}
}
else
{
lean_object* v_val_2237_; 
lean_del_object(v___x_2229_);
v_val_2237_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_val_2237_);
lean_dec_ref(v___x_2231_);
v___y_2220_ = v___y_2225_;
v_val_2221_ = v_val_2237_;
goto v___jp_2219_;
}
}
else
{
lean_object* v_val_2238_; 
lean_del_object(v___x_2229_);
v_val_2238_ = lean_ctor_get(v_a_2227_, 0);
lean_inc(v_val_2238_);
lean_dec_ref(v_a_2227_);
v___y_2220_ = v___y_2225_;
v_val_2221_ = v_val_2238_;
goto v___jp_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_2248_, lean_object* v_n_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_2248_, v_n_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v_firsts_2248_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_2254_, lean_object* v_x_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
if (lean_obj_tag(v_x_2255_) == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = l_List_reverse___redArg(v_x_2256_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
else
{
lean_object* v_head_2262_; lean_object* v_tail_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2281_; 
v_head_2262_ = lean_ctor_get(v_x_2255_, 0);
v_tail_2263_ = lean_ctor_get(v_x_2255_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_x_2255_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2265_ = v_x_2255_;
v_isShared_2266_ = v_isSharedCheck_2281_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_tail_2263_);
lean_inc(v_head_2262_);
lean_dec(v_x_2255_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2281_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; 
v___x_2267_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_2254_, v_head_2262_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref(v___x_2267_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v_x_2256_);
lean_ctor_set(v___x_2265_, 0, v_a_2268_);
v___x_2270_ = v___x_2265_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2268_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_x_2256_);
v___x_2270_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
v_x_2255_ = v_tail_2263_;
v_x_2256_ = v___x_2270_;
goto _start;
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_del_object(v___x_2265_);
lean_dec(v_tail_2263_);
lean_dec(v_x_2256_);
v_a_2273_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2267_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2267_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2282_, v_x_2283_, v_x_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v_a_2282_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_2289_, lean_object* v___x_2290_, lean_object* v___x_2291_, lean_object* v_a_2292_, lean_object* v_b_2293_){
_start:
{
lean_object* v_it_2295_; lean_object* v_startInclusive_2296_; lean_object* v_endExclusive_2297_; 
if (lean_obj_tag(v_a_2292_) == 0)
{
lean_object* v_currPos_2302_; lean_object* v_searcher_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2329_; 
v_currPos_2302_ = lean_ctor_get(v_a_2292_, 0);
v_searcher_2303_ = lean_ctor_get(v_a_2292_, 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_a_2292_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2305_ = v_a_2292_;
v_isShared_2306_ = v_isSharedCheck_2329_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_searcher_2303_);
lean_inc(v_currPos_2302_);
lean_dec(v_a_2292_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2329_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_startInclusive_2307_; lean_object* v_endExclusive_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_startInclusive_2307_ = lean_ctor_get(v___x_2290_, 1);
v_endExclusive_2308_ = lean_ctor_get(v___x_2290_, 2);
v___x_2309_ = lean_nat_sub(v_endExclusive_2308_, v_startInclusive_2307_);
v___x_2310_ = lean_nat_dec_eq(v_searcher_2303_, v___x_2309_);
lean_dec(v___x_2309_);
if (v___x_2310_ == 0)
{
uint32_t v___x_2311_; uint32_t v___x_2312_; uint8_t v___x_2313_; 
v___x_2311_ = 10;
v___x_2312_ = lean_string_utf8_get_fast(v_val_2289_, v_searcher_2303_);
v___x_2313_ = lean_uint32_dec_eq(v___x_2312_, v___x_2311_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = lean_string_utf8_next_fast(v_val_2289_, v_searcher_2303_);
lean_dec(v_searcher_2303_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2314_);
v___x_2316_ = v___x_2305_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_currPos_2302_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
v_a_2292_ = v___x_2316_;
goto _start;
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v_slice_2322_; lean_object* v_nextIt_2324_; 
v___x_2319_ = lean_string_utf8_next_fast(v_val_2289_, v_searcher_2303_);
v___x_2320_ = lean_nat_sub(v___x_2319_, v_searcher_2303_);
v___x_2321_ = lean_nat_add(v_searcher_2303_, v___x_2320_);
lean_dec(v___x_2320_);
v_slice_2322_ = l_String_Slice_subslice_x21(v___x_2290_, v_currPos_2302_, v_searcher_2303_);
lean_inc(v___x_2321_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2321_);
lean_ctor_set(v___x_2305_, 0, v___x_2321_);
v_nextIt_2324_ = v___x_2305_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2321_);
v_nextIt_2324_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v_startInclusive_2325_; lean_object* v_endExclusive_2326_; 
v_startInclusive_2325_ = lean_ctor_get(v_slice_2322_, 0);
lean_inc(v_startInclusive_2325_);
v_endExclusive_2326_ = lean_ctor_get(v_slice_2322_, 1);
lean_inc(v_endExclusive_2326_);
lean_dec_ref(v_slice_2322_);
v_it_2295_ = v_nextIt_2324_;
v_startInclusive_2296_ = v_startInclusive_2325_;
v_endExclusive_2297_ = v_endExclusive_2326_;
goto v___jp_2294_;
}
}
}
else
{
lean_object* v___x_2328_; 
lean_del_object(v___x_2305_);
lean_dec(v_searcher_2303_);
v___x_2328_ = lean_box(1);
lean_inc(v___x_2291_);
v_it_2295_ = v___x_2328_;
v_startInclusive_2296_ = v_currPos_2302_;
v_endExclusive_2297_ = v___x_2291_;
goto v___jp_2294_;
}
}
}
else
{
lean_dec(v___x_2291_);
return v_b_2293_;
}
v___jp_2294_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_string_utf8_extract(v_val_2289_, v_startInclusive_2296_, v_endExclusive_2297_);
lean_dec(v_endExclusive_2297_);
lean_dec(v_startInclusive_2296_);
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
v___x_2300_ = lean_array_push(v_b_2293_, v___x_2299_);
v_a_2292_ = v_it_2295_;
v_b_2293_ = v___x_2300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2330_, lean_object* v___x_2331_, lean_object* v___x_2332_, lean_object* v_a_2333_, lean_object* v_b_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2330_, v___x_2331_, v___x_2332_, v_a_2333_, v_b_2334_);
lean_dec_ref(v___x_2331_);
lean_dec_ref(v_val_2330_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(lean_object* v_init_2336_, lean_object* v_x_2337_){
_start:
{
if (lean_obj_tag(v_x_2337_) == 0)
{
lean_object* v_k_2338_; lean_object* v_l_2339_; lean_object* v_r_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_k_2338_ = lean_ctor_get(v_x_2337_, 1);
lean_inc(v_k_2338_);
v_l_2339_ = lean_ctor_get(v_x_2337_, 3);
lean_inc(v_l_2339_);
v_r_2340_ = lean_ctor_get(v_x_2337_, 4);
lean_inc(v_r_2340_);
lean_dec_ref(v_x_2337_);
v___x_2341_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_2336_, v_l_2339_);
v___x_2342_ = lean_array_push(v___x_2341_, v_k_2338_);
v_init_2336_ = v___x_2342_;
v_x_2337_ = v_r_2340_;
goto _start;
}
else
{
return v_init_2336_;
}
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2351_ = l_Lean_stringToMessageData(v___x_2350_);
return v___x_2351_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2354_ = l_Lean_stringToMessageData(v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2359_ = l_Lean_MessageData_ofFormat(v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = l_List_reverse___redArg(v_x_2363_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
else
{
lean_object* v_head_2369_; lean_object* v_tail_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2467_; 
v_head_2369_ = lean_ctor_get(v_x_2362_, 0);
v_tail_2370_ = lean_ctor_get(v_x_2362_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_x_2362_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2372_ = v_x_2362_;
v_isShared_2373_ = v_isSharedCheck_2467_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_tail_2370_);
lean_inc(v_head_2369_);
lean_dec(v_x_2362_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2467_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v_snd_2387_; lean_object* v_fst_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2466_; 
v_snd_2387_ = lean_ctor_get(v_head_2369_, 1);
v_fst_2388_ = lean_ctor_get(v_head_2369_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_head_2369_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2390_ = v_head_2369_;
v_isShared_2391_ = v_isSharedCheck_2466_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_snd_2387_);
lean_inc(v_fst_2388_);
lean_dec(v_head_2369_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2466_;
goto v_resetjp_2389_;
}
v___jp_2374_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___y_2375_);
lean_ctor_set(v___x_2379_, 1, v___y_2378_);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v___y_2377_);
v___x_2381_ = l_Lean_MessageData_nestD(v___x_2380_);
lean_inc_ref(v___y_2376_);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___y_2376_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 1, v_x_2363_);
lean_ctor_set(v___x_2372_, 0, v___x_2382_);
v___x_2384_ = v___x_2372_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_x_2363_);
v___x_2384_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v_x_2362_ = v_tail_2370_;
v_x_2363_ = v___x_2384_;
goto _start;
}
}
v_resetjp_2389_:
{
lean_object* v_fst_2392_; lean_object* v_snd_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2465_; 
v_fst_2392_ = lean_ctor_get(v_snd_2387_, 0);
v_snd_2393_ = lean_ctor_get(v_snd_2387_, 1);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_snd_2387_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2395_ = v_snd_2387_;
v_isShared_2396_ = v_isSharedCheck_2465_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_snd_2393_);
lean_inc(v_fst_2392_);
lean_dec(v_snd_2387_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2465_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v_a_2420_; lean_object* v___y_2436_; lean_object* v___x_2445_; 
v___x_2445_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2361_, v_fst_2388_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_MessageData_nil;
v_a_2420_ = v___x_2446_;
goto v___jp_2419_;
}
else
{
lean_object* v_val_2447_; 
v_val_2447_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_val_2447_);
lean_dec_ref(v___x_2445_);
if (lean_obj_tag(v_val_2447_) == 0)
{
lean_object* v_size_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v_size_2448_ = lean_ctor_get(v_val_2447_, 0);
v___x_2449_ = lean_mk_empty_array_with_capacity(v_size_2448_);
v___x_2450_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v___x_2449_, v_val_2447_);
v___x_2455_ = lean_array_get_size(v___x_2450_);
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_nat_dec_eq(v___x_2455_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___y_2461_; uint8_t v___x_2463_; 
v___x_2458_ = lean_unsigned_to_nat(1u);
v___x_2459_ = lean_nat_sub(v___x_2455_, v___x_2458_);
v___x_2463_ = lean_nat_dec_le(v___x_2456_, v___x_2459_);
if (v___x_2463_ == 0)
{
lean_inc(v___x_2459_);
v___y_2461_ = v___x_2459_;
goto v___jp_2460_;
}
else
{
v___y_2461_ = v___x_2456_;
goto v___jp_2460_;
}
v___jp_2460_:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_nat_dec_le(v___y_2461_, v___x_2459_);
if (v___x_2462_ == 0)
{
lean_dec(v___x_2459_);
lean_inc(v___y_2461_);
v___y_2452_ = v___y_2461_;
v___y_2453_ = v___y_2461_;
goto v___jp_2451_;
}
else
{
v___y_2452_ = v___y_2461_;
v___y_2453_ = v___x_2459_;
goto v___jp_2451_;
}
}
}
else
{
v___y_2436_ = v___x_2450_;
goto v___jp_2435_;
}
v___jp_2451_:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2450_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
v___y_2436_ = v___x_2454_;
goto v___jp_2435_;
}
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_MessageData_nil;
v_a_2420_ = v___x_2464_;
goto v___jp_2419_;
}
}
v___jp_2397_:
{
lean_object* v___x_2403_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set_tag(v___x_2395_, 7);
lean_ctor_set(v___x_2395_, 1, v___y_2401_);
lean_ctor_set(v___x_2395_, 0, v___y_2399_);
v___x_2403_ = v___x_2395_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___y_2399_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v___y_2401_);
v___x_2403_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
if (lean_obj_tag(v_snd_2393_) == 0)
{
lean_object* v___x_2404_; 
lean_del_object(v___x_2390_);
v___x_2404_ = l_Lean_MessageData_nil;
v___y_2375_ = v___x_2403_;
v___y_2376_ = v___y_2398_;
v___y_2377_ = v___y_2400_;
v___y_2378_ = v___x_2404_;
goto v___jp_2374_;
}
else
{
lean_object* v_val_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v_val_2405_ = lean_ctor_get(v_snd_2393_, 0);
lean_inc_n(v_val_2405_, 2);
lean_dec_ref(v_snd_2393_);
v___x_2406_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2407_ = lean_unsigned_to_nat(0u);
v___x_2408_ = lean_string_utf8_byte_size(v_val_2405_);
v___x_2409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2409_, 0, v_val_2405_);
lean_ctor_set(v___x_2409_, 1, v___x_2407_);
lean_ctor_set(v___x_2409_, 2, v___x_2408_);
v___x_2410_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2409_);
v___x_2411_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2412_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2405_, v___x_2409_, v___x_2408_, v___x_2410_, v___x_2411_);
lean_dec_ref(v___x_2409_);
lean_dec(v_val_2405_);
v___x_2413_ = lean_array_to_list(v___x_2412_);
v___x_2414_ = l_Lean_MessageData_joinSep(v___x_2413_, v___x_2406_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 7);
lean_ctor_set(v___x_2390_, 1, v___x_2414_);
lean_ctor_set(v___x_2390_, 0, v___x_2406_);
v___x_2416_ = v___x_2390_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
v___y_2375_ = v___x_2403_;
v___y_2376_ = v___y_2398_;
v___y_2377_ = v___y_2400_;
v___y_2378_ = v___x_2416_;
goto v___jp_2374_;
}
}
}
}
v___jp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2421_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2422_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2388_);
v___x_2423_ = l_Lean_MessageData_ofName(v_fst_2388_);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v___x_2422_);
v___x_2426_ = 1;
v___x_2427_ = l_Lean_Name_toString(v_fst_2388_, v___x_2426_);
v___x_2428_ = lean_string_dec_eq(v___x_2427_, v_fst_2392_);
lean_dec_ref(v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2429_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2430_ = l_Lean_stringToMessageData(v_fst_2392_);
v___x_2431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___y_2398_ = v___x_2421_;
v___y_2399_ = v___x_2425_;
v___y_2400_ = v_a_2420_;
v___y_2401_ = v___x_2433_;
goto v___jp_2397_;
}
else
{
lean_object* v___x_2434_; 
lean_dec(v_fst_2392_);
v___x_2434_ = l_Lean_MessageData_nil;
v___y_2398_ = v___x_2421_;
v___y_2399_ = v___x_2425_;
v___y_2400_ = v_a_2420_;
v___y_2401_ = v___x_2434_;
goto v___jp_2397_;
}
}
v___jp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_array_to_list(v___y_2436_);
v___x_2438_ = lean_box(0);
v___x_2439_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2360_, v___x_2437_, v___x_2438_, v___y_2364_, v___y_2365_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2442_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2443_ = l_Lean_MessageData_joinSep(v_a_2440_, v___x_2442_);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2441_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v_a_2420_ = v___x_2444_;
goto v___jp_2419_;
}
else
{
lean_del_object(v___x_2395_);
lean_dec(v_snd_2393_);
lean_dec(v_fst_2392_);
lean_del_object(v___x_2390_);
lean_dec(v_fst_2388_);
lean_del_object(v___x_2372_);
lean_dec(v_tail_2370_);
lean_dec(v_x_2363_);
return v___x_2439_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_x_2470_, lean_object* v_x_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2468_, v_a_2469_, v_x_2470_, v_x_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v_a_2469_);
lean_dec(v_a_2468_);
return v_res_2475_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(uint8_t v___y_2477_, uint8_t v_suppressElabErrors_2478_, lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 1)
{
lean_object* v_pre_2480_; 
v_pre_2480_ = lean_ctor_get(v_x_2479_, 0);
if (lean_obj_tag(v_pre_2480_) == 0)
{
lean_object* v_str_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_str_2481_ = lean_ctor_get(v_x_2479_, 1);
v___x_2482_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0));
v___x_2483_ = lean_string_dec_eq(v_str_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
return v___y_2477_;
}
else
{
return v_suppressElabErrors_2478_;
}
}
else
{
return v___y_2477_;
}
}
else
{
return v___y_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed(lean_object* v___y_2484_, lean_object* v_suppressElabErrors_2485_, lean_object* v_x_2486_){
_start:
{
uint8_t v___y_19652__boxed_2487_; uint8_t v_suppressElabErrors_boxed_2488_; uint8_t v_res_2489_; lean_object* v_r_2490_; 
v___y_19652__boxed_2487_ = lean_unbox(v___y_2484_);
v_suppressElabErrors_boxed_2488_ = lean_unbox(v_suppressElabErrors_2485_);
v_res_2489_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(v___y_19652__boxed_2487_, v_suppressElabErrors_boxed_2488_, v_x_2486_);
lean_dec(v_x_2486_);
v_r_2490_ = lean_box(v_res_2489_);
return v_r_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(lean_object* v_ref_2491_, lean_object* v_msgData_2492_, uint8_t v_severity_2493_, uint8_t v_isSilent_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___y_2499_; uint8_t v___y_2500_; lean_object* v___y_2501_; uint8_t v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; uint8_t v___y_2562_; lean_object* v___y_2563_; uint8_t v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2590_; uint8_t v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2593_; lean_object* v___y_2594_; uint8_t v___y_2598_; uint8_t v___y_2599_; uint8_t v___y_2600_; uint8_t v___x_2615_; uint8_t v___y_2617_; uint8_t v___y_2618_; uint8_t v___y_2619_; uint8_t v___y_2621_; uint8_t v___x_2633_; 
v___x_2615_ = 2;
v___x_2633_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2493_, v___x_2615_);
if (v___x_2633_ == 0)
{
v___y_2621_ = v___x_2633_;
goto v___jp_2620_;
}
else
{
uint8_t v___x_2634_; 
lean_inc_ref(v_msgData_2492_);
v___x_2634_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2492_);
v___y_2621_ = v___x_2634_;
goto v___jp_2620_;
}
v___jp_2498_:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_Elab_Command_getScope___redArg(v___y_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2509_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref(v___x_2507_);
v___x_2509_ = l_Lean_Elab_Command_getScope___redArg(v___y_2506_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2544_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2544_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2544_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v_currNamespace_2515_; lean_object* v_openDecls_2516_; lean_object* v_env_2517_; lean_object* v_messages_2518_; lean_object* v_scopes_2519_; lean_object* v_usedQuotCtxts_2520_; lean_object* v_nextMacroScope_2521_; lean_object* v_maxRecDepth_2522_; lean_object* v_ngen_2523_; lean_object* v_auxDeclNGen_2524_; lean_object* v_infoState_2525_; lean_object* v_traceState_2526_; lean_object* v_snapshotTasks_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2543_; 
v___x_2514_ = lean_st_ref_take(v___y_2506_);
v_currNamespace_2515_ = lean_ctor_get(v_a_2508_, 2);
lean_inc(v_currNamespace_2515_);
lean_dec(v_a_2508_);
v_openDecls_2516_ = lean_ctor_get(v_a_2510_, 3);
lean_inc(v_openDecls_2516_);
lean_dec(v_a_2510_);
v_env_2517_ = lean_ctor_get(v___x_2514_, 0);
v_messages_2518_ = lean_ctor_get(v___x_2514_, 1);
v_scopes_2519_ = lean_ctor_get(v___x_2514_, 2);
v_usedQuotCtxts_2520_ = lean_ctor_get(v___x_2514_, 3);
v_nextMacroScope_2521_ = lean_ctor_get(v___x_2514_, 4);
v_maxRecDepth_2522_ = lean_ctor_get(v___x_2514_, 5);
v_ngen_2523_ = lean_ctor_get(v___x_2514_, 6);
v_auxDeclNGen_2524_ = lean_ctor_get(v___x_2514_, 7);
v_infoState_2525_ = lean_ctor_get(v___x_2514_, 8);
v_traceState_2526_ = lean_ctor_get(v___x_2514_, 9);
v_snapshotTasks_2527_ = lean_ctor_get(v___x_2514_, 10);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2529_ = v___x_2514_;
v_isShared_2530_ = v_isSharedCheck_2543_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_snapshotTasks_2527_);
lean_inc(v_traceState_2526_);
lean_inc(v_infoState_2525_);
lean_inc(v_auxDeclNGen_2524_);
lean_inc(v_ngen_2523_);
lean_inc(v_maxRecDepth_2522_);
lean_inc(v_nextMacroScope_2521_);
lean_inc(v_usedQuotCtxts_2520_);
lean_inc(v_scopes_2519_);
lean_inc(v_messages_2518_);
lean_inc(v_env_2517_);
lean_dec(v___x_2514_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2543_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v_currNamespace_2515_);
lean_ctor_set(v___x_2531_, 1, v_openDecls_2516_);
v___x_2532_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v___y_2503_);
lean_inc_ref(v___y_2505_);
lean_inc_ref(v___y_2499_);
v___x_2533_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2533_, 0, v___y_2499_);
lean_ctor_set(v___x_2533_, 1, v___y_2504_);
lean_ctor_set(v___x_2533_, 2, v___y_2501_);
lean_ctor_set(v___x_2533_, 3, v___y_2505_);
lean_ctor_set(v___x_2533_, 4, v___x_2532_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*5, v___y_2500_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*5 + 1, v___y_2502_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*5 + 2, v_isSilent_2494_);
v___x_2534_ = l_Lean_MessageLog_add(v___x_2533_, v_messages_2518_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2534_);
v___x_2536_ = v___x_2529_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_env_2517_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_scopes_2519_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_usedQuotCtxts_2520_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v_nextMacroScope_2521_);
lean_ctor_set(v_reuseFailAlloc_2542_, 5, v_maxRecDepth_2522_);
lean_ctor_set(v_reuseFailAlloc_2542_, 6, v_ngen_2523_);
lean_ctor_set(v_reuseFailAlloc_2542_, 7, v_auxDeclNGen_2524_);
lean_ctor_set(v_reuseFailAlloc_2542_, 8, v_infoState_2525_);
lean_ctor_set(v_reuseFailAlloc_2542_, 9, v_traceState_2526_);
lean_ctor_set(v_reuseFailAlloc_2542_, 10, v_snapshotTasks_2527_);
v___x_2536_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2537_ = lean_st_ref_set(v___y_2506_, v___x_2536_);
v___x_2538_ = lean_box(0);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2538_);
v___x_2540_ = v___x_2512_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2508_);
lean_dec_ref(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2501_);
v_a_2545_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2509_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2509_);
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
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2501_);
v_a_2553_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2507_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2507_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
v___jp_2561_:
{
lean_object* v_fileName_2567_; lean_object* v_fileMap_2568_; uint8_t v_suppressElabErrors_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2588_; 
v_fileName_2567_ = lean_ctor_get(v___y_2495_, 0);
v_fileMap_2568_ = lean_ctor_get(v___y_2495_, 1);
v_suppressElabErrors_2569_ = lean_ctor_get_uint8(v___y_2495_, sizeof(void*)*10);
v___x_2570_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2492_);
v___x_2571_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2570_, v___y_2496_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2588_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2588_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_inc_ref_n(v_fileMap_2568_, 2);
v___x_2576_ = l_Lean_FileMap_toPosition(v_fileMap_2568_, v___y_2563_);
lean_dec(v___y_2563_);
v___x_2577_ = l_Lean_FileMap_toPosition(v_fileMap_2568_, v___y_2566_);
lean_dec(v___y_2566_);
v___x_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
v___x_2579_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2569_ == 0)
{
lean_del_object(v___x_2574_);
v___y_2499_ = v_fileName_2567_;
v___y_2500_ = v___y_2564_;
v___y_2501_ = v___x_2578_;
v___y_2502_ = v___y_2565_;
v___y_2503_ = v_a_2572_;
v___y_2504_ = v___x_2576_;
v___y_2505_ = v___x_2579_;
v___y_2506_ = v___y_2496_;
goto v___jp_2498_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; uint8_t v___x_2583_; 
v___x_2580_ = lean_box(v___y_2562_);
v___x_2581_ = lean_box(v_suppressElabErrors_2569_);
v___f_2582_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2582_, 0, v___x_2580_);
lean_closure_set(v___f_2582_, 1, v___x_2581_);
lean_inc(v_a_2572_);
v___x_2583_ = l_Lean_MessageData_hasTag(v___f_2582_, v_a_2572_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_dec_ref(v___x_2578_);
lean_dec_ref(v___x_2576_);
lean_dec(v_a_2572_);
v___x_2584_ = lean_box(0);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2584_);
v___x_2586_ = v___x_2574_;
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
else
{
lean_del_object(v___x_2574_);
v___y_2499_ = v_fileName_2567_;
v___y_2500_ = v___y_2564_;
v___y_2501_ = v___x_2578_;
v___y_2502_ = v___y_2565_;
v___y_2503_ = v_a_2572_;
v___y_2504_ = v___x_2576_;
v___y_2505_ = v___x_2579_;
v___y_2506_ = v___y_2496_;
goto v___jp_2498_;
}
}
}
}
v___jp_2589_:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_Syntax_getTailPos_x3f(v___y_2592_, v___y_2591_);
lean_dec(v___y_2592_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_inc(v___y_2594_);
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2594_;
v___y_2564_ = v___y_2591_;
v___y_2565_ = v___y_2593_;
v___y_2566_ = v___y_2594_;
goto v___jp_2561_;
}
else
{
lean_object* v_val_2596_; 
v_val_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_val_2596_);
lean_dec_ref(v___x_2595_);
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2594_;
v___y_2564_ = v___y_2591_;
v___y_2565_ = v___y_2593_;
v___y_2566_ = v_val_2596_;
goto v___jp_2561_;
}
}
v___jp_2597_:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Elab_Command_getRef___redArg(v___y_2495_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v_ref_2603_; lean_object* v___x_2604_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2601_);
v_ref_2603_ = l_Lean_replaceRef(v_ref_2491_, v_a_2602_);
lean_dec(v_a_2602_);
v___x_2604_ = l_Lean_Syntax_getPos_x3f(v_ref_2603_, v___y_2599_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2599_;
v___y_2592_ = v_ref_2603_;
v___y_2593_ = v___y_2600_;
v___y_2594_ = v___x_2605_;
goto v___jp_2589_;
}
else
{
lean_object* v_val_2606_; 
v_val_2606_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_val_2606_);
lean_dec_ref(v___x_2604_);
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2599_;
v___y_2592_ = v_ref_2603_;
v___y_2593_ = v___y_2600_;
v___y_2594_ = v_val_2606_;
goto v___jp_2589_;
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_msgData_2492_);
v_a_2607_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2601_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2601_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
v___jp_2616_:
{
if (v___y_2619_ == 0)
{
v___y_2598_ = v___y_2617_;
v___y_2599_ = v___y_2618_;
v___y_2600_ = v_severity_2493_;
goto v___jp_2597_;
}
else
{
v___y_2598_ = v___y_2617_;
v___y_2599_ = v___y_2618_;
v___y_2600_ = v___x_2615_;
goto v___jp_2597_;
}
}
v___jp_2620_:
{
if (v___y_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v_scopes_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v_opts_2626_; uint8_t v___x_2627_; uint8_t v___x_2628_; 
v___x_2622_ = lean_st_ref_get(v___y_2496_);
v_scopes_2623_ = lean_ctor_get(v___x_2622_, 2);
lean_inc(v_scopes_2623_);
lean_dec(v___x_2622_);
v___x_2624_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2625_ = l_List_head_x21___redArg(v___x_2624_, v_scopes_2623_);
lean_dec(v_scopes_2623_);
v_opts_2626_ = lean_ctor_get(v___x_2625_, 1);
lean_inc_ref(v_opts_2626_);
lean_dec(v___x_2625_);
v___x_2627_ = 1;
v___x_2628_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2493_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_dec_ref(v_opts_2626_);
v___y_2617_ = v___y_2621_;
v___y_2618_ = v___y_2621_;
v___y_2619_ = v___x_2628_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2629_; uint8_t v___x_2630_; 
v___x_2629_ = l_Lean_warningAsError;
v___x_2630_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2626_, v___x_2629_);
lean_dec_ref(v_opts_2626_);
v___y_2617_ = v___y_2621_;
v___y_2618_ = v___y_2621_;
v___y_2619_ = v___x_2630_;
goto v___jp_2616_;
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v_msgData_2492_);
v___x_2631_ = lean_box(0);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___boxed(lean_object* v_ref_2635_, lean_object* v_msgData_2636_, lean_object* v_severity_2637_, lean_object* v_isSilent_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v_severity_boxed_2642_; uint8_t v_isSilent_boxed_2643_; lean_object* v_res_2644_; 
v_severity_boxed_2642_ = lean_unbox(v_severity_2637_);
v_isSilent_boxed_2643_ = lean_unbox(v_isSilent_2638_);
v_res_2644_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(v_ref_2635_, v_msgData_2636_, v_severity_boxed_2642_, v_isSilent_boxed_2643_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v_ref_2635_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(lean_object* v_msgData_2645_, uint8_t v_severity_2646_, uint8_t v_isSilent_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_Elab_Command_getRef___redArg(v___y_2648_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2651_);
v___x_2653_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(v_a_2652_, v_msgData_2645_, v_severity_2646_, v_isSilent_2647_, v___y_2648_, v___y_2649_);
lean_dec(v_a_2652_);
return v___x_2653_;
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_msgData_2645_);
v_a_2654_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2651_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2651_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27___boxed(lean_object* v_msgData_2662_, lean_object* v_severity_2663_, lean_object* v_isSilent_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
uint8_t v_severity_boxed_2668_; uint8_t v_isSilent_boxed_2669_; lean_object* v_res_2670_; 
v_severity_boxed_2668_ = lean_unbox(v_severity_2663_);
v_isSilent_boxed_2669_ = lean_unbox(v_isSilent_2664_);
v_res_2670_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(v_msgData_2662_, v_severity_boxed_2668_, v_isSilent_boxed_2669_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = 0;
v___x_2676_ = 0;
v___x_2677_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(v_msgData_2671_, v___x_2675_, v___x_2676_, v___y_2672_, v___y_2673_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(lean_object* v_init_2683_, lean_object* v_x_2684_){
_start:
{
if (lean_obj_tag(v_x_2684_) == 0)
{
lean_object* v_k_2685_; lean_object* v_v_2686_; lean_object* v_l_2687_; lean_object* v_r_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_k_2685_ = lean_ctor_get(v_x_2684_, 1);
v_v_2686_ = lean_ctor_get(v_x_2684_, 2);
v_l_2687_ = lean_ctor_get(v_x_2684_, 3);
v_r_2688_ = lean_ctor_get(v_x_2684_, 4);
v___x_2689_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_2683_, v_l_2687_);
lean_inc(v_v_2686_);
lean_inc(v_k_2685_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_k_2685_);
lean_ctor_set(v___x_2690_, 1, v_v_2686_);
v___x_2691_ = lean_array_push(v___x_2689_, v___x_2690_);
v_init_2683_ = v___x_2691_;
v_x_2684_ = v_r_2688_;
goto _start;
}
else
{
return v_init_2683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26___boxed(lean_object* v_init_2693_, lean_object* v_x_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_2693_, v_x_2694_);
lean_dec(v_x_2694_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(lean_object* v_as_2696_, size_t v_sz_2697_, size_t v_i_2698_, lean_object* v_b_2699_){
_start:
{
uint8_t v___x_2701_; 
v___x_2701_ = lean_usize_dec_lt(v_i_2698_, v_sz_2697_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v_b_2699_);
return v___x_2702_;
}
else
{
lean_object* v_a_2703_; lean_object* v_fst_2704_; lean_object* v_snd_2705_; lean_object* v_found_2706_; size_t v___x_2707_; size_t v___x_2708_; 
v_a_2703_ = lean_array_uget_borrowed(v_as_2696_, v_i_2698_);
v_fst_2704_ = lean_ctor_get(v_a_2703_, 0);
v_snd_2705_ = lean_ctor_get(v_a_2703_, 1);
lean_inc(v_snd_2705_);
lean_inc(v_fst_2704_);
v_found_2706_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2704_, v_snd_2705_, v_b_2699_);
v___x_2707_ = ((size_t)1ULL);
v___x_2708_ = lean_usize_add(v_i_2698_, v___x_2707_);
v_i_2698_ = v___x_2708_;
v_b_2699_ = v_found_2706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg___boxed(lean_object* v_as_2710_, lean_object* v_sz_2711_, lean_object* v_i_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_){
_start:
{
size_t v_sz_boxed_2715_; size_t v_i_boxed_2716_; lean_object* v_res_2717_; 
v_sz_boxed_2715_ = lean_unbox_usize(v_sz_2711_);
lean_dec(v_sz_2711_);
v_i_boxed_2716_ = lean_unbox_usize(v_i_2712_);
lean_dec(v_i_2712_);
v_res_2717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_as_2710_, v_sz_boxed_2715_, v_i_boxed_2716_, v_b_2713_);
lean_dec_ref(v_as_2710_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_as_2718_, size_t v_sz_2719_, size_t v_i_2720_, lean_object* v_b_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_usize_dec_lt(v_i_2720_, v_sz_2719_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_b_2721_);
return v___x_2726_;
}
else
{
lean_object* v_a_2727_; size_t v_sz_2728_; size_t v___x_2729_; lean_object* v___x_2730_; 
v_a_2727_ = lean_array_uget_borrowed(v_as_2718_, v_i_2720_);
v_sz_2728_ = lean_array_size(v_a_2727_);
v___x_2729_ = ((size_t)0ULL);
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_a_2727_, v_sz_2728_, v___x_2729_, v_b_2721_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; size_t v___x_2732_; size_t v___x_2733_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2720_, v___x_2732_);
v_i_2720_ = v___x_2733_;
v_b_2721_ = v_a_2731_;
goto _start;
}
else
{
return v___x_2730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_as_2735_, lean_object* v_sz_2736_, lean_object* v_i_2737_, lean_object* v_b_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
size_t v_sz_boxed_2742_; size_t v_i_boxed_2743_; lean_object* v_res_2744_; 
v_sz_boxed_2742_ = lean_unbox_usize(v_sz_2736_);
lean_dec(v_sz_2736_);
v_i_boxed_2743_ = lean_unbox_usize(v_i_2737_);
lean_dec(v_i_2737_);
v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_as_2735_, v_sz_boxed_2742_, v_i_boxed_2743_, v_b_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec_ref(v_as_2735_);
return v_res_2744_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(uint8_t v___x_2745_, lean_object* v_x1_2746_, lean_object* v_x2_2747_){
_start:
{
lean_object* v_fst_2748_; lean_object* v_fst_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v_fst_2748_ = lean_ctor_get(v_x1_2746_, 0);
lean_inc(v_fst_2748_);
lean_dec_ref(v_x1_2746_);
v_fst_2749_ = lean_ctor_get(v_x2_2747_, 0);
lean_inc(v_fst_2749_);
lean_dec_ref(v_x2_2747_);
v___x_2750_ = l_Lean_Name_toString(v_fst_2748_, v___x_2745_);
v___x_2751_ = l_Lean_Name_toString(v_fst_2749_, v___x_2745_);
v___x_2752_ = lean_string_dec_lt(v___x_2750_, v___x_2751_);
lean_dec_ref(v___x_2751_);
lean_dec_ref(v___x_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed(lean_object* v___x_2753_, lean_object* v_x1_2754_, lean_object* v_x2_2755_){
_start:
{
uint8_t v___x_20027__boxed_2756_; uint8_t v_res_2757_; lean_object* v_r_2758_; 
v___x_20027__boxed_2756_ = lean_unbox(v___x_2753_);
v_res_2757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(v___x_20027__boxed_2756_, v_x1_2754_, v_x2_2755_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_as_2759_, lean_object* v_lo_2760_, lean_object* v_hi_2761_){
_start:
{
uint8_t v___x_2762_; 
v___x_2762_ = lean_nat_dec_lt(v_lo_2760_, v_hi_2761_);
if (v___x_2762_ == 0)
{
lean_dec(v_lo_2760_);
return v_as_2759_;
}
else
{
lean_object* v___x_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; uint8_t v___x_2768_; 
v___x_2763_ = lean_box(v___x_2762_);
v___f_2764_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2764_, 0, v___x_2763_);
lean_inc(v_lo_2760_);
v___x_2765_ = l_Array_qpartition___redArg(v_as_2759_, v___f_2764_, v_lo_2760_, v_hi_2761_);
v_fst_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_fst_2766_);
v_snd_2767_ = lean_ctor_get(v___x_2765_, 1);
lean_inc(v_snd_2767_);
lean_dec_ref(v___x_2765_);
v___x_2768_ = lean_nat_dec_le(v_hi_2761_, v_fst_2766_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_snd_2767_, v_lo_2760_, v_fst_2766_);
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_nat_add(v_fst_2766_, v___x_2770_);
lean_dec(v_fst_2766_);
v_as_2759_ = v___x_2769_;
v_lo_2760_ = v___x_2771_;
goto _start;
}
else
{
lean_dec(v_fst_2766_);
lean_dec(v_lo_2760_);
return v_snd_2767_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_as_2773_, lean_object* v_lo_2774_, lean_object* v_hi_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_as_2773_, v_lo_2774_, v_hi_2775_);
lean_dec(v_hi_2775_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object* v_init_2777_, lean_object* v_x_2778_){
_start:
{
if (lean_obj_tag(v_x_2778_) == 0)
{
lean_object* v_k_2780_; lean_object* v_v_2781_; lean_object* v_l_2782_; lean_object* v_r_2783_; lean_object* v___x_2784_; lean_object* v_a_2785_; lean_object* v_a_2786_; lean_object* v___x_2787_; 
v_k_2780_ = lean_ctor_get(v_x_2778_, 1);
lean_inc(v_k_2780_);
v_v_2781_ = lean_ctor_get(v_x_2778_, 2);
lean_inc(v_v_2781_);
v_l_2782_ = lean_ctor_get(v_x_2778_, 3);
lean_inc(v_l_2782_);
v_r_2783_ = lean_ctor_get(v_x_2778_, 4);
lean_inc(v_r_2783_);
lean_dec_ref(v_x_2778_);
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_2777_, v_l_2782_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
v_a_2786_ = lean_ctor_get(v_a_2785_, 0);
lean_inc(v_a_2786_);
lean_dec(v_a_2785_);
v___x_2787_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2780_, v_v_2781_, v_a_2786_);
v_init_2777_ = v___x_2787_;
v_x_2778_ = v_r_2783_;
goto _start;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_init_2777_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object* v_init_2791_, lean_object* v_x_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_2791_, v_x_2792_);
return v_res_2794_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_box(1);
v___x_2796_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___y_2803_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___x_2818_; lean_object* v_env_2819_; lean_object* v___x_2820_; lean_object* v_toEnvExtension_2821_; lean_object* v_asyncMode_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v_a_2828_; lean_object* v_a_2830_; lean_object* v_a_2853_; 
v___x_2818_ = lean_st_ref_get(v___y_2800_);
v_env_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc_ref_n(v_env_2819_, 2);
lean_dec(v___x_2818_);
v___x_2820_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2821_ = lean_ctor_get(v___x_2820_, 0);
v_asyncMode_2822_ = lean_ctor_get(v_toEnvExtension_2821_, 2);
v___x_2823_ = lean_box(1);
v___x_2824_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2825_ = lean_box(0);
v___x_2826_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2823_, v___x_2820_, v_env_2819_, v_asyncMode_2822_, v___x_2825_);
v___x_2827_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v___x_2823_, v___x_2826_);
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v___x_2827_);
v_a_2853_ = lean_ctor_get(v_a_2828_, 0);
lean_inc(v_a_2853_);
lean_dec(v_a_2828_);
v_a_2830_ = v_a_2853_;
goto v___jp_2829_;
v___jp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_array_to_list(v___y_2803_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
v___jp_2806_:
{
lean_object* v___x_2811_; 
lean_dec(v___y_2807_);
v___x_2811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
v___y_2803_ = v___x_2811_;
goto v___jp_2802_;
}
v___jp_2812_:
{
uint8_t v___x_2817_; 
v___x_2817_ = lean_nat_dec_le(v___y_2816_, v___y_2813_);
if (v___x_2817_ == 0)
{
lean_dec(v___y_2813_);
lean_inc(v___y_2816_);
v___y_2807_ = v___y_2814_;
v___y_2808_ = v___y_2815_;
v___y_2809_ = v___y_2816_;
v___y_2810_ = v___y_2816_;
goto v___jp_2806_;
}
else
{
v___y_2807_ = v___y_2814_;
v___y_2808_ = v___y_2815_;
v___y_2809_ = v___y_2816_;
v___y_2810_ = v___y_2813_;
goto v___jp_2806_;
}
}
v___jp_2829_:
{
lean_object* v___x_2831_; lean_object* v_importedEntries_2832_; size_t v_sz_2833_; size_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2831_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2824_, v_toEnvExtension_2821_, v_env_2819_, v_asyncMode_2822_, v___x_2825_);
v_importedEntries_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc_ref(v_importedEntries_2832_);
lean_dec(v___x_2831_);
v_sz_2833_ = lean_array_size(v_importedEntries_2832_);
v___x_2834_ = ((size_t)0ULL);
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_importedEntries_2832_, v_sz_2833_, v___x_2834_, v_a_2830_, v___y_2799_, v___y_2800_);
lean_dec_ref(v_importedEntries_2832_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v_arr_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v___x_2838_, v_a_2836_);
lean_dec(v_a_2836_);
v___x_2840_ = lean_array_get_size(v_arr_2839_);
v___x_2841_ = lean_nat_dec_eq(v___x_2840_, v___x_2837_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2842_ = lean_unsigned_to_nat(1u);
v___x_2843_ = lean_nat_sub(v___x_2840_, v___x_2842_);
v___x_2844_ = lean_nat_dec_le(v___x_2837_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_inc(v___x_2843_);
v___y_2813_ = v___x_2843_;
v___y_2814_ = v___x_2840_;
v___y_2815_ = v_arr_2839_;
v___y_2816_ = v___x_2843_;
goto v___jp_2812_;
}
else
{
v___y_2813_ = v___x_2843_;
v___y_2814_ = v___x_2840_;
v___y_2815_ = v_arr_2839_;
v___y_2816_ = v___x_2837_;
goto v___jp_2812_;
}
}
else
{
v___y_2803_ = v_arr_2839_;
goto v___jp_2802_;
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2835_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2835_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2858_, lean_object* v_k_2859_, lean_object* v_fallback_2860_){
_start:
{
if (lean_obj_tag(v_t_2858_) == 0)
{
lean_object* v_k_2861_; lean_object* v_v_2862_; lean_object* v_l_2863_; lean_object* v_r_2864_; uint8_t v___x_2865_; 
v_k_2861_ = lean_ctor_get(v_t_2858_, 1);
v_v_2862_ = lean_ctor_get(v_t_2858_, 2);
v_l_2863_ = lean_ctor_get(v_t_2858_, 3);
v_r_2864_ = lean_ctor_get(v_t_2858_, 4);
v___x_2865_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2859_, v_k_2861_);
switch(v___x_2865_)
{
case 0:
{
v_t_2858_ = v_l_2863_;
goto _start;
}
case 1:
{
lean_inc(v_v_2862_);
return v_v_2862_;
}
default: 
{
v_t_2858_ = v_r_2864_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2860_);
return v_fallback_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2868_, lean_object* v_k_2869_, lean_object* v_fallback_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2868_, v_k_2869_, v_fallback_2870_);
lean_dec(v_fallback_2870_);
lean_dec(v_k_2869_);
lean_dec(v_t_2868_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2872_, size_t v_sz_2873_, size_t v_i_2874_, lean_object* v_b_2875_){
_start:
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_usize_dec_lt(v_i_2874_, v_sz_2873_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_b_2875_);
return v___x_2878_;
}
else
{
lean_object* v_a_2879_; lean_object* v_fst_2880_; lean_object* v_snd_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; size_t v___x_2886_; size_t v___x_2887_; 
v_a_2879_ = lean_array_uget_borrowed(v_as_2872_, v_i_2874_);
v_fst_2880_ = lean_ctor_get(v_a_2879_, 0);
v_snd_2881_ = lean_ctor_get(v_a_2879_, 1);
v___x_2882_ = l_Lean_NameSet_empty;
v___x_2883_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2875_, v_snd_2881_, v___x_2882_);
lean_inc(v_fst_2880_);
v___x_2884_ = l_Lean_NameSet_insert(v___x_2883_, v_fst_2880_);
lean_inc(v_snd_2881_);
v___x_2885_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2881_, v___x_2884_, v_b_2875_);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2874_, v___x_2886_);
v_i_2874_ = v___x_2887_;
v_b_2875_ = v___x_2885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2889_, lean_object* v_sz_2890_, lean_object* v_i_2891_, lean_object* v_b_2892_, lean_object* v___y_2893_){
_start:
{
size_t v_sz_boxed_2894_; size_t v_i_boxed_2895_; lean_object* v_res_2896_; 
v_sz_boxed_2894_ = lean_unbox_usize(v_sz_2890_);
lean_dec(v_sz_2890_);
v_i_boxed_2895_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_res_2896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2889_, v_sz_boxed_2894_, v_i_boxed_2895_, v_b_2892_);
lean_dec_ref(v_as_2889_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2897_, size_t v_sz_2898_, size_t v_i_2899_, lean_object* v_b_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_usize_dec_lt(v_i_2899_, v_sz_2898_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v_b_2900_);
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; size_t v_sz_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v_a_2906_ = lean_array_uget_borrowed(v_as_2897_, v_i_2899_);
v_sz_2907_ = lean_array_size(v_a_2906_);
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2906_, v_sz_2907_, v___x_2908_, v_b_2900_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; size_t v___x_2911_; size_t v___x_2912_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___x_2909_);
v___x_2911_ = ((size_t)1ULL);
v___x_2912_ = lean_usize_add(v_i_2899_, v___x_2911_);
v_i_2899_ = v___x_2912_;
v_b_2900_ = v_a_2910_;
goto _start;
}
else
{
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2914_, lean_object* v_sz_2915_, lean_object* v_i_2916_, lean_object* v_b_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
size_t v_sz_boxed_2921_; size_t v_i_boxed_2922_; lean_object* v_res_2923_; 
v_sz_boxed_2921_ = lean_unbox_usize(v_sz_2915_);
lean_dec(v_sz_2915_);
v_i_boxed_2922_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_res_2923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2914_, v_sz_boxed_2921_, v_i_boxed_2922_, v_b_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec_ref(v_as_2914_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2924_, size_t v_i_2925_, size_t v_stop_2926_, lean_object* v_b_2927_){
_start:
{
uint8_t v___x_2928_; 
v___x_2928_ = lean_usize_dec_eq(v_i_2925_, v_stop_2926_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; 
v___x_2929_ = lean_array_uget_borrowed(v_as_2924_, v_i_2925_);
v_fst_2930_ = lean_ctor_get(v___x_2929_, 0);
v_snd_2931_ = lean_ctor_get(v___x_2929_, 1);
lean_inc(v_snd_2931_);
lean_inc(v_fst_2930_);
v___x_2932_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2930_, v_snd_2931_, v_b_2927_);
v___x_2933_ = ((size_t)1ULL);
v___x_2934_ = lean_usize_add(v_i_2925_, v___x_2933_);
v_i_2925_ = v___x_2934_;
v_b_2927_ = v___x_2932_;
goto _start;
}
else
{
return v_b_2927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2936_, lean_object* v_i_2937_, lean_object* v_stop_2938_, lean_object* v_b_2939_){
_start:
{
size_t v_i_boxed_2940_; size_t v_stop_boxed_2941_; lean_object* v_res_2942_; 
v_i_boxed_2940_ = lean_unbox_usize(v_i_2937_);
lean_dec(v_i_2937_);
v_stop_boxed_2941_ = lean_unbox_usize(v_stop_2938_);
lean_dec(v_stop_2938_);
v_res_2942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2936_, v_i_boxed_2940_, v_stop_boxed_2941_, v_b_2939_);
lean_dec_ref(v_as_2936_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2943_, size_t v_i_2944_, size_t v_stop_2945_, lean_object* v_b_2946_){
_start:
{
lean_object* v___y_2948_; uint8_t v___x_2952_; 
v___x_2952_ = lean_usize_dec_eq(v_i_2944_, v_stop_2945_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2953_ = lean_array_uget_borrowed(v_as_2943_, v_i_2944_);
v___x_2954_ = lean_unsigned_to_nat(0u);
v___x_2955_ = lean_array_get_size(v___x_2953_);
v___x_2956_ = lean_nat_dec_lt(v___x_2954_, v___x_2955_);
if (v___x_2956_ == 0)
{
v___y_2948_ = v_b_2946_;
goto v___jp_2947_;
}
else
{
uint8_t v___x_2957_; 
v___x_2957_ = lean_nat_dec_le(v___x_2955_, v___x_2955_);
if (v___x_2957_ == 0)
{
if (v___x_2956_ == 0)
{
v___y_2948_ = v_b_2946_;
goto v___jp_2947_;
}
else
{
size_t v___x_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = ((size_t)0ULL);
v___x_2959_ = lean_usize_of_nat(v___x_2955_);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2953_, v___x_2958_, v___x_2959_, v_b_2946_);
v___y_2948_ = v___x_2960_;
goto v___jp_2947_;
}
}
else
{
size_t v___x_2961_; size_t v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = ((size_t)0ULL);
v___x_2962_ = lean_usize_of_nat(v___x_2955_);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2953_, v___x_2961_, v___x_2962_, v_b_2946_);
v___y_2948_ = v___x_2963_;
goto v___jp_2947_;
}
}
}
else
{
return v_b_2946_;
}
v___jp_2947_:
{
size_t v___x_2949_; size_t v___x_2950_; 
v___x_2949_ = ((size_t)1ULL);
v___x_2950_ = lean_usize_add(v_i_2944_, v___x_2949_);
v_i_2944_ = v___x_2950_;
v_b_2946_ = v___y_2948_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2964_, lean_object* v_i_2965_, lean_object* v_stop_2966_, lean_object* v_b_2967_){
_start:
{
size_t v_i_boxed_2968_; size_t v_stop_boxed_2969_; lean_object* v_res_2970_; 
v_i_boxed_2968_ = lean_unbox_usize(v_i_2965_);
lean_dec(v_i_2965_);
v_stop_boxed_2969_ = lean_unbox_usize(v_stop_2966_);
lean_dec(v_stop_2966_);
v_res_2970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2964_, v_i_boxed_2968_, v_stop_boxed_2969_, v_b_2967_);
lean_dec_ref(v_as_2964_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v_env_2974_; lean_object* v___x_2975_; lean_object* v_ext_2976_; lean_object* v_toEnvExtension_2977_; lean_object* v_asyncMode_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_categories_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2973_ = lean_st_ref_get(v___y_2971_);
v_env_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc_ref_n(v_env_2974_, 2);
lean_dec(v___x_2973_);
v___x_2975_ = l_Lean_Parser_parserExtension;
v_ext_2976_ = lean_ctor_get(v___x_2975_, 1);
v_toEnvExtension_2977_ = lean_ctor_get(v_ext_2976_, 0);
v_asyncMode_2978_ = lean_ctor_get(v_toEnvExtension_2977_, 2);
v___x_2979_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2980_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2979_, v___x_2975_, v_env_2974_, v_asyncMode_2978_);
v_categories_2981_ = lean_ctor_get(v___x_2980_, 2);
lean_inc_ref(v_categories_2981_);
lean_dec(v___x_2980_);
v___x_2982_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2983_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2981_, v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 1)
{
lean_object* v_val_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3021_; 
v_val_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_3021_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_val_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3021_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___y_2989_; lean_object* v___x_2998_; lean_object* v_toEnvExtension_2999_; lean_object* v_exportEntriesFn_3000_; lean_object* v_asyncMode_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v_importedEntries_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v_exported_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_2998_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2999_ = lean_ctor_get(v___x_2998_, 0);
v_exportEntriesFn_3000_ = lean_ctor_get(v___x_2998_, 4);
v_asyncMode_3001_ = lean_ctor_get(v_toEnvExtension_2999_, 2);
v___x_3002_ = lean_box(1);
v___x_3003_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3004_ = lean_box(0);
lean_inc_ref_n(v_env_2974_, 2);
v___x_3005_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3003_, v_toEnvExtension_2999_, v_env_2974_, v_asyncMode_3001_, v___x_3004_);
v_importedEntries_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc_ref(v_importedEntries_3006_);
lean_dec(v___x_3005_);
v___x_3007_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3002_, v___x_2998_, v_env_2974_, v_asyncMode_3001_, v___x_3004_);
lean_inc_ref(v_exportEntriesFn_3000_);
v___x_3008_ = lean_apply_2(v_exportEntriesFn_3000_, v_env_2974_, v___x_3007_);
v_exported_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_exported_3009_);
lean_dec_ref(v___x_3008_);
v___x_3010_ = lean_array_push(v_importedEntries_3006_, v_exported_3009_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_array_get_size(v___x_3010_);
v___x_3013_ = lean_nat_dec_lt(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_dec_ref(v___x_3010_);
v___y_2989_ = v___x_3002_;
goto v___jp_2988_;
}
else
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_nat_dec_le(v___x_3012_, v___x_3012_);
if (v___x_3014_ == 0)
{
if (v___x_3013_ == 0)
{
lean_dec_ref(v___x_3010_);
v___y_2989_ = v___x_3002_;
goto v___jp_2988_;
}
else
{
size_t v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_of_nat(v___x_3012_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3010_, v___x_3015_, v___x_3016_, v___x_3002_);
lean_dec_ref(v___x_3010_);
v___y_2989_ = v___x_3017_;
goto v___jp_2988_;
}
}
else
{
size_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = ((size_t)0ULL);
v___x_3019_ = lean_usize_of_nat(v___x_3012_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3010_, v___x_3018_, v___x_3019_, v___x_3002_);
lean_dec_ref(v___x_3010_);
v___y_2989_ = v___x_3020_;
goto v___jp_2988_;
}
}
v___jp_2988_:
{
lean_object* v_tables_2990_; lean_object* v_leadingTable_2991_; lean_object* v_trailingTable_2992_; lean_object* v_firstTokens_2993_; lean_object* v_firstTokens_2994_; lean_object* v___x_2996_; 
v_tables_2990_ = lean_ctor_get(v_val_2984_, 2);
v_leadingTable_2991_ = lean_ctor_get(v_tables_2990_, 0);
v_trailingTable_2992_ = lean_ctor_get(v_tables_2990_, 2);
lean_inc(v_trailingTable_2992_);
lean_inc(v_leadingTable_2991_);
lean_inc(v_val_2984_);
v_firstTokens_2993_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2984_, v_leadingTable_2991_, v___y_2989_);
v_firstTokens_2994_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2984_, v_trailingTable_2992_, v_firstTokens_2993_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 0);
lean_ctor_set(v___x_2986_, 0, v_firstTokens_2994_);
v___x_2996_ = v___x_2986_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_firstTokens_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec(v___x_2983_);
lean_dec_ref(v_env_2974_);
v___x_3022_ = lean_box(1);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3024_);
lean_dec(v___y_3024_);
return v_res_3026_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_box(1);
v___x_3028_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3027_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_3031_ = l_Lean_stringToMessageData(v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_env_3038_; lean_object* v_env_3039_; lean_object* v_env_3040_; lean_object* v___x_3041_; lean_object* v_toEnvExtension_3042_; lean_object* v_exportEntriesFn_3043_; lean_object* v_asyncMode_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_importedEntries_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3101_; 
v___x_3035_ = lean_st_ref_get(v_a_3033_);
v___x_3036_ = lean_st_ref_get(v_a_3033_);
v___x_3037_ = lean_st_ref_get(v_a_3033_);
v_env_3038_ = lean_ctor_get(v___x_3035_, 0);
lean_inc_ref(v_env_3038_);
lean_dec(v___x_3035_);
v_env_3039_ = lean_ctor_get(v___x_3036_, 0);
lean_inc_ref(v_env_3039_);
lean_dec(v___x_3036_);
v_env_3040_ = lean_ctor_get(v___x_3037_, 0);
lean_inc_ref(v_env_3040_);
lean_dec(v___x_3037_);
v___x_3041_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3042_ = lean_ctor_get(v___x_3041_, 0);
v_exportEntriesFn_3043_ = lean_ctor_get(v___x_3041_, 4);
v_asyncMode_3044_ = lean_ctor_get(v_toEnvExtension_3042_, 2);
v___x_3045_ = lean_box(1);
v___x_3046_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3047_ = lean_box(0);
v___x_3048_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3046_, v_toEnvExtension_3042_, v_env_3038_, v_asyncMode_3044_, v___x_3047_);
v_importedEntries_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v___x_3048_, 1);
lean_dec(v_unused_3102_);
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3101_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_importedEntries_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3101_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v_exported_3055_; lean_object* v___x_3056_; size_t v_sz_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3053_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3045_, v___x_3041_, v_env_3040_, v_asyncMode_3044_, v___x_3047_);
lean_inc_ref(v_exportEntriesFn_3043_);
v___x_3054_ = lean_apply_2(v_exportEntriesFn_3043_, v_env_3039_, v___x_3053_);
v_exported_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_exported_3055_);
lean_dec_ref(v___x_3054_);
v___x_3056_ = lean_array_push(v_importedEntries_3049_, v_exported_3055_);
v_sz_3057_ = lean_array_size(v___x_3056_);
v___x_3058_ = ((size_t)0ULL);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_3056_, v_sz_3057_, v___x_3058_, v___x_3045_, v_a_3032_, v_a_3033_);
lean_dec_ref(v___x_3056_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; lean_object* v_a_3062_; lean_object* v___x_3063_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref(v___x_3059_);
v___x_3061_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_3033_);
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref(v___x_3061_);
v___x_3063_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref(v___x_3063_);
v___x_3065_ = lean_box(0);
v___x_3066_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3062_, v_a_3060_, v_a_3064_, v___x_3065_, v_a_3032_, v_a_3033_);
lean_dec(v_a_3060_);
lean_dec(v_a_3062_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3072_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref(v___x_3066_);
v___x_3068_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_3069_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_3070_ = l_Lean_MessageData_joinSep(v_a_3067_, v___x_3069_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 7);
lean_ctor_set(v___x_3051_, 1, v___x_3070_);
lean_ctor_set(v___x_3051_, 0, v___x_3069_);
v___x_3072_ = v___x_3051_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3069_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = l_Lean_MessageData_nestD(v___x_3072_);
v___x_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3068_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_3074_, v_a_3032_, v_a_3033_);
return v___x_3075_;
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_del_object(v___x_3051_);
v_a_3077_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3066_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3066_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_a_3062_);
lean_dec(v_a_3060_);
lean_del_object(v___x_3051_);
v_a_3085_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3063_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3063_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_del_object(v___x_3051_);
v_a_3093_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3059_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3059_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3108_, v_a_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_3112_, v_a_3113_, v_a_3114_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec(v___stx_3112_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_3117_, lean_object* v_t_3118_, lean_object* v_k_3119_, lean_object* v_fallback_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3118_, v_k_3119_, v_fallback_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_3122_, lean_object* v_t_3123_, lean_object* v_k_3124_, lean_object* v_fallback_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_3122_, v_t_3123_, v_k_3124_, v_fallback_3125_);
lean_dec(v_fallback_3125_);
lean_dec(v_k_3124_);
lean_dec(v_t_3123_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_3127_, size_t v_sz_3128_, size_t v_i_3129_, lean_object* v_b_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3127_, v_sz_3128_, v_i_3129_, v_b_3130_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_3135_, lean_object* v_sz_3136_, lean_object* v_i_3137_, lean_object* v_b_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
size_t v_sz_boxed_3142_; size_t v_i_boxed_3143_; lean_object* v_res_3144_; 
v_sz_boxed_3142_ = lean_unbox_usize(v_sz_3136_);
lean_dec(v_sz_3136_);
v_i_boxed_3143_ = lean_unbox_usize(v_i_3137_);
lean_dec(v_i_3137_);
v_res_3144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_3135_, v_sz_boxed_3142_, v_i_boxed_3143_, v_b_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec_ref(v_as_3135_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_3153_, lean_object* v___x_3154_, lean_object* v___x_3155_, lean_object* v_inst_3156_, lean_object* v_R_3157_, lean_object* v_a_3158_, lean_object* v_b_3159_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3153_, v___x_3154_, v___x_3155_, v_a_3158_, v_b_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_inst_3164_, lean_object* v_R_3165_, lean_object* v_a_3166_, lean_object* v_b_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_3161_, v___x_3162_, v___x_3163_, v_inst_3164_, v_R_3165_, v_a_3166_, v_b_3167_);
lean_dec_ref(v___x_3162_);
lean_dec_ref(v_val_3161_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_3169_, lean_object* v_t_3170_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_3169_, v_t_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_3172_, lean_object* v_as_3173_, lean_object* v_lo_3174_, lean_object* v_hi_3175_, lean_object* v_w_3176_, lean_object* v_hlo_3177_, lean_object* v_hhi_3178_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_as_3173_, v_lo_3174_, v_hi_3175_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_3180_, lean_object* v_as_3181_, lean_object* v_lo_3182_, lean_object* v_hi_3183_, lean_object* v_w_3184_, lean_object* v_hlo_3185_, lean_object* v_hhi_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_3180_, v_as_3181_, v_lo_3182_, v_hi_3183_, v_w_3184_, v_hlo_3185_, v_hhi_3186_);
lean_dec(v_hi_3183_);
lean_dec(v_n_3180_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_3188_, lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3189_, v_x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3192_, lean_object* v_x_3193_, lean_object* v_x_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_3192_, v_x_3193_, v_x_3194_);
lean_dec(v_x_3194_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3196_, v___y_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b2_3206_, lean_object* v_k_3207_, lean_object* v_v_3208_, lean_object* v_t_3209_, lean_object* v_hl_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_3207_, v_v_3208_, v_t_3209_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_as_3212_, lean_object* v_as_x27_3213_, lean_object* v_b_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_as_x27_3213_, v_b_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_as_3217_, lean_object* v_as_x27_3218_, lean_object* v_b_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_as_3217_, v_as_x27_3218_, v_b_3219_, v_a_3220_);
lean_dec(v_as_3217_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_00_u03b4_3222_, lean_object* v_t_3223_, lean_object* v_k_3224_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_3223_, v_k_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___boxed(lean_object* v_00_u03b4_3226_, lean_object* v_t_3227_, lean_object* v_k_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v_00_u03b4_3226_, v_t_3227_, v_k_3228_);
lean_dec(v_k_3228_);
lean_dec(v_t_3227_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(lean_object* v_00_u03b2_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_3231_, v_x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___boxed(lean_object* v_00_u03b2_3234_, lean_object* v_x_3235_, lean_object* v_x_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(v_00_u03b2_3234_, v_x_3235_, v_x_3236_);
lean_dec(v_x_3236_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3238_, size_t v_sz_3239_, size_t v_i_3240_, lean_object* v_b_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_as_3238_, v_sz_3239_, v_i_3240_, v_b_3241_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3246_, lean_object* v_sz_3247_, lean_object* v_i_3248_, lean_object* v_b_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
size_t v_sz_boxed_3253_; size_t v_i_boxed_3254_; lean_object* v_res_3255_; 
v_sz_boxed_3253_ = lean_unbox_usize(v_sz_3247_);
lean_dec(v_sz_3247_);
v_i_boxed_3254_ = lean_unbox_usize(v_i_3248_);
lean_dec(v_i_3248_);
v_res_3255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3246_, v_sz_boxed_3253_, v_i_boxed_3254_, v_b_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec_ref(v_as_3246_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_init_3256_, lean_object* v_t_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_3256_, v_t_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_init_3259_, lean_object* v_t_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_init_3259_, v_t_3260_);
lean_dec(v_t_3260_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_n_3262_, lean_object* v_as_3263_, lean_object* v_lo_3264_, lean_object* v_hi_3265_, lean_object* v_w_3266_, lean_object* v_hlo_3267_, lean_object* v_hhi_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_as_3263_, v_lo_3264_, v_hi_3265_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_n_3270_, lean_object* v_as_3271_, lean_object* v_lo_3272_, lean_object* v_hi_3273_, lean_object* v_w_3274_, lean_object* v_hlo_3275_, lean_object* v_hhi_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_n_3270_, v_as_3271_, v_lo_3272_, v_hi_3273_, v_w_3274_, v_hlo_3275_, v_hhi_3276_);
lean_dec(v_hi_3273_);
lean_dec(v_n_3270_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object* v_init_3278_, lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_3278_, v_x_3279_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object* v_init_3284_, lean_object* v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(v_init_3284_, v_x_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3290_, lean_object* v_x_3291_, size_t v_x_3292_, lean_object* v_x_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3291_, v_x_3292_, v_x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_){
_start:
{
size_t v_x_20662__boxed_3299_; lean_object* v_res_3300_; 
v_x_20662__boxed_3299_ = lean_unbox_usize(v_x_3297_);
lean_dec(v_x_3297_);
v_res_3300_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3295_, v_x_3296_, v_x_20662__boxed_3299_, v_x_3298_);
lean_dec(v_x_3298_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3301_, lean_object* v_k_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3301_, v_k_3302_, v_x_3303_, v_x_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3307_, lean_object* v_k_3308_, lean_object* v_x_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3307_, v_k_3308_, v_x_3309_, v_x_3310_, v_x_3311_);
lean_dec_ref(v_k_3308_);
lean_dec_ref(v_as_3307_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object* v_00_u03b2_3313_, lean_object* v_m_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_3314_, v_a_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object* v_00_u03b2_3317_, lean_object* v_m_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(v_00_u03b2_3317_, v_m_3318_, v_a_3319_);
lean_dec(v_a_3319_);
lean_dec_ref(v_m_3318_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3321_, lean_object* v_keys_3322_, lean_object* v_vals_3323_, lean_object* v_heq_3324_, lean_object* v_i_3325_, lean_object* v_k_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3322_, v_vals_3323_, v_i_3325_, v_k_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_keys_3329_, lean_object* v_vals_3330_, lean_object* v_heq_3331_, lean_object* v_i_3332_, lean_object* v_k_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3328_, v_keys_3329_, v_vals_3330_, v_heq_3331_, v_i_3332_, v_k_3333_);
lean_dec(v_k_3333_);
lean_dec_ref(v_vals_3330_);
lean_dec_ref(v_keys_3329_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object* v_00_u03b2_3335_, lean_object* v_a_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_3336_, v_x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object* v_00_u03b2_3339_, lean_object* v_a_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(v_00_u03b2_3339_, v_a_3340_, v_x_3341_);
lean_dec(v_x_3341_);
lean_dec(v_a_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3357_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3360_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3361_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3357_, v___x_3358_, v___x_3359_, v___x_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3368_ = l_Lean_addBuiltinDocString(v___x_3366_, v___x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3399_ = l_Lean_addBuiltinDeclarationRanges(v___x_3397_, v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, uint8_t v_includeUnnamed_3405_, lean_object* v_x_3406_, lean_object* v_____s_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_fst_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3466_; 
v_fst_3413_ = lean_ctor_get(v_x_3406_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_x_3406_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v_x_3406_, 1);
lean_dec(v_unused_3467_);
v___x_3415_ = v_x_3406_;
v_isShared_3416_ = v_isSharedCheck_3466_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_fst_3413_);
lean_dec(v_x_3406_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3466_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_userName_3418_; lean_object* v___y_3419_; lean_object* v___x_3451_; 
lean_inc(v_fst_3413_);
lean_inc_ref(v_env_3402_);
v___x_3451_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3402_, v_fst_3413_);
if (lean_obj_tag(v___x_3451_) == 1)
{
lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3459_; 
lean_del_object(v___x_3415_);
lean_dec(v_fst_3413_);
lean_dec_ref(v_env_3402_);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; 
v_unused_3460_ = lean_ctor_get(v___x_3451_, 0);
lean_dec(v_unused_3460_);
v___x_3453_ = v___x_3451_;
v_isShared_3454_ = v_isSharedCheck_3459_;
goto v_resetjp_3452_;
}
else
{
lean_dec(v___x_3451_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3459_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v_____s_3407_);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_____s_3407_);
v___x_3456_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
}
else
{
lean_object* v___x_3461_; 
lean_dec(v___x_3451_);
v___x_3461_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_a_3404_, v_fst_3413_);
if (lean_obj_tag(v___x_3461_) == 1)
{
lean_object* v_val_3462_; 
v_val_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_val_3462_);
lean_dec_ref(v___x_3461_);
v_userName_3418_ = v_val_3462_;
v___y_3419_ = v___y_3410_;
goto v___jp_3417_;
}
else
{
lean_dec(v___x_3461_);
if (v_includeUnnamed_3405_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_del_object(v___x_3415_);
lean_dec(v_fst_3413_);
lean_dec_ref(v_env_3402_);
v___x_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_____s_3407_);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
return v___x_3464_;
}
else
{
lean_object* v___x_3465_; 
lean_inc(v_fst_3413_);
v___x_3465_ = l_Lean_Name_toString(v_fst_3413_, v_includeUnnamed_3405_);
v_userName_3418_ = v___x_3465_;
v___y_3419_ = v___y_3410_;
goto v___jp_3417_;
}
}
}
v___jp_3417_:
{
uint8_t v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = 1;
lean_inc(v_fst_3413_);
lean_inc_ref(v_env_3402_);
v___x_3421_ = l_Lean_findDocString_x3f(v_env_3402_, v_fst_3413_, v___x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3435_; 
lean_del_object(v___x_3415_);
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3435_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3435_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3426_ = l_Lean_NameSet_empty;
v___x_3427_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3403_, v_fst_3413_, v___x_3426_);
lean_inc(v_fst_3413_);
v___x_3428_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3402_, v_fst_3413_);
v___x_3429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3429_, 0, v_fst_3413_);
lean_ctor_set(v___x_3429_, 1, v_userName_3418_);
lean_ctor_set(v___x_3429_, 2, v___x_3427_);
lean_ctor_set(v___x_3429_, 3, v_a_3422_);
lean_ctor_set(v___x_3429_, 4, v___x_3428_);
v___x_3430_ = lean_array_push(v_____s_3407_, v___x_3429_);
v___x_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3431_);
v___x_3433_ = v___x_3424_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3450_; 
lean_dec_ref(v_userName_3418_);
lean_dec(v_fst_3413_);
lean_dec_ref(v_____s_3407_);
lean_dec_ref(v_env_3402_);
v_a_3436_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3438_ = v___x_3421_;
v_isShared_3439_ = v_isSharedCheck_3450_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3421_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3450_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_ref_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v_ref_3440_ = lean_ctor_get(v___y_3419_, 5);
v___x_3441_ = lean_io_error_to_string(v_a_3436_);
v___x_3442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
v___x_3443_ = l_Lean_MessageData_ofFormat(v___x_3442_);
lean_inc(v_ref_3440_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v___x_3443_);
lean_ctor_set(v___x_3415_, 0, v_ref_3440_);
v___x_3445_ = v___x_3415_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_ref_3440_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3445_);
v___x_3447_ = v___x_3438_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_includeUnnamed_3471_, lean_object* v_x_3472_, lean_object* v_____s_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
uint8_t v_includeUnnamed_boxed_3479_; lean_object* v_res_3480_; 
v_includeUnnamed_boxed_3479_ = lean_unbox(v_includeUnnamed_3471_);
v_res_3480_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3468_, v_a_3469_, v_a_3470_, v_includeUnnamed_boxed_3479_, v_x_3472_, v_____s_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v_a_3470_);
lean_dec(v_a_3469_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3481_, size_t v_sz_3482_, size_t v_i_3483_, lean_object* v_b_3484_){
_start:
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_usize_dec_lt(v_i_3483_, v_sz_3482_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_b_3484_);
return v___x_3487_;
}
else
{
lean_object* v_a_3488_; lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; size_t v___x_3495_; size_t v___x_3496_; 
v_a_3488_ = lean_array_uget_borrowed(v_as_3481_, v_i_3483_);
v_fst_3489_ = lean_ctor_get(v_a_3488_, 0);
v_snd_3490_ = lean_ctor_get(v_a_3488_, 1);
v___x_3491_ = l_Lean_NameSet_empty;
v___x_3492_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3484_, v_fst_3489_, v___x_3491_);
lean_inc(v_snd_3490_);
v___x_3493_ = l_Lean_NameSet_insert(v___x_3492_, v_snd_3490_);
lean_inc(v_fst_3489_);
v___x_3494_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3489_, v___x_3493_, v_b_3484_);
v___x_3495_ = ((size_t)1ULL);
v___x_3496_ = lean_usize_add(v_i_3483_, v___x_3495_);
v_i_3483_ = v___x_3496_;
v_b_3484_ = v___x_3494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3498_, lean_object* v_sz_3499_, lean_object* v_i_3500_, lean_object* v_b_3501_, lean_object* v___y_3502_){
_start:
{
size_t v_sz_boxed_3503_; size_t v_i_boxed_3504_; lean_object* v_res_3505_; 
v_sz_boxed_3503_ = lean_unbox_usize(v_sz_3499_);
lean_dec(v_sz_3499_);
v_i_boxed_3504_ = lean_unbox_usize(v_i_3500_);
lean_dec(v_i_3500_);
v_res_3505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3498_, v_sz_boxed_3503_, v_i_boxed_3504_, v_b_3501_);
lean_dec_ref(v_as_3498_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3506_, size_t v_sz_3507_, size_t v_i_3508_, lean_object* v_b_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v___x_3515_; 
v___x_3515_ = lean_usize_dec_lt(v_i_3508_, v_sz_3507_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_b_3509_);
return v___x_3516_;
}
else
{
lean_object* v_a_3517_; size_t v_sz_3518_; size_t v___x_3519_; lean_object* v___x_3520_; 
v_a_3517_ = lean_array_uget_borrowed(v_as_3506_, v_i_3508_);
v_sz_3518_ = lean_array_size(v_a_3517_);
v___x_3519_ = ((size_t)0ULL);
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3517_, v_sz_3518_, v___x_3519_, v_b_3509_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; size_t v___x_3522_; size_t v___x_3523_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = ((size_t)1ULL);
v___x_3523_ = lean_usize_add(v_i_3508_, v___x_3522_);
v_i_3508_ = v___x_3523_;
v_b_3509_ = v_a_3521_;
goto _start;
}
else
{
return v___x_3520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3525_, lean_object* v_sz_3526_, lean_object* v_i_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
size_t v_sz_boxed_3534_; size_t v_i_boxed_3535_; lean_object* v_res_3536_; 
v_sz_boxed_3534_ = lean_unbox_usize(v_sz_3526_);
lean_dec(v_sz_3526_);
v_i_boxed_3535_ = lean_unbox_usize(v_i_3527_);
lean_dec(v_i_3527_);
v_res_3536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3525_, v_sz_boxed_3534_, v_i_boxed_3535_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec_ref(v_as_3525_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3537_, lean_object* v_keys_3538_, lean_object* v_vals_3539_, lean_object* v_i_3540_, lean_object* v_acc_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3547_ = lean_array_get_size(v_keys_3538_);
v___x_3548_ = lean_nat_dec_lt(v_i_3540_, v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec(v_i_3540_);
lean_dec_ref(v_f_3537_);
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_acc_3541_);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
else
{
lean_object* v_k_3551_; lean_object* v_v_3552_; lean_object* v___x_3553_; 
v_k_3551_ = lean_array_fget_borrowed(v_keys_3538_, v_i_3540_);
v_v_3552_ = lean_array_fget_borrowed(v_vals_3539_, v_i_3540_);
lean_inc_ref(v_f_3537_);
lean_inc(v___y_3545_);
lean_inc_ref(v___y_3544_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v_v_3552_);
lean_inc(v_k_3551_);
v___x_3553_ = lean_apply_8(v_f_3537_, v_acc_3541_, v_k_3551_, v_v_3552_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, lean_box(0));
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
if (lean_obj_tag(v_a_3554_) == 0)
{
lean_dec_ref(v_a_3554_);
lean_dec(v_i_3540_);
lean_dec_ref(v_f_3537_);
return v___x_3553_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_dec_ref(v___x_3553_);
v_a_3555_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref(v_a_3554_);
v___x_3556_ = lean_unsigned_to_nat(1u);
v___x_3557_ = lean_nat_add(v_i_3540_, v___x_3556_);
lean_dec(v_i_3540_);
v_i_3540_ = v___x_3557_;
v_acc_3541_ = v_a_3555_;
goto _start;
}
}
else
{
lean_dec(v_i_3540_);
lean_dec_ref(v_f_3537_);
return v___x_3553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3559_, lean_object* v_keys_3560_, lean_object* v_vals_3561_, lean_object* v_i_3562_, lean_object* v_acc_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3559_, v_keys_3560_, v_vals_3561_, v_i_3562_, v_acc_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec_ref(v_vals_3561_);
lean_dec_ref(v_keys_3560_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
if (lean_obj_tag(v_x_3571_) == 0)
{
lean_object* v_es_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3600_; 
v_es_3578_ = lean_ctor_get(v_x_3571_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_x_3571_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3580_ = v_x_3571_;
v_isShared_3581_ = v_isSharedCheck_3600_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_es_3578_);
lean_dec(v_x_3571_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3600_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3582_ = lean_unsigned_to_nat(0u);
v___x_3583_ = lean_array_get_size(v_es_3578_);
v___x_3584_ = lean_nat_dec_lt(v___x_3582_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3586_; 
lean_dec_ref(v_es_3578_);
lean_dec_ref(v_f_3570_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set_tag(v___x_3580_, 1);
lean_ctor_set(v___x_3580_, 0, v_x_3572_);
v___x_3586_ = v___x_3580_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_x_3572_);
v___x_3586_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
}
else
{
uint8_t v___x_3589_; 
v___x_3589_ = lean_nat_dec_le(v___x_3583_, v___x_3583_);
if (v___x_3589_ == 0)
{
if (v___x_3584_ == 0)
{
lean_object* v___x_3591_; 
lean_dec_ref(v_es_3578_);
lean_dec_ref(v_f_3570_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set_tag(v___x_3580_, 1);
lean_ctor_set(v___x_3580_, 0, v_x_3572_);
v___x_3591_ = v___x_3580_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_x_3572_);
v___x_3591_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
}
else
{
size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; 
lean_del_object(v___x_3580_);
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = lean_usize_of_nat(v___x_3583_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3570_, v_es_3578_, v___x_3594_, v___x_3595_, v_x_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec_ref(v_es_3578_);
return v___x_3596_;
}
}
else
{
size_t v___x_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
lean_del_object(v___x_3580_);
v___x_3597_ = ((size_t)0ULL);
v___x_3598_ = lean_usize_of_nat(v___x_3583_);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3570_, v_es_3578_, v___x_3597_, v___x_3598_, v_x_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec_ref(v_es_3578_);
return v___x_3599_;
}
}
}
}
else
{
lean_object* v_ks_3601_; lean_object* v_vs_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_ks_3601_ = lean_ctor_get(v_x_3571_, 0);
lean_inc_ref(v_ks_3601_);
v_vs_3602_ = lean_ctor_get(v_x_3571_, 1);
lean_inc_ref(v_vs_3602_);
lean_dec_ref(v_x_3571_);
v___x_3603_ = lean_unsigned_to_nat(0u);
v___x_3604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3570_, v_ks_3601_, v_vs_3602_, v___x_3603_, v_x_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec_ref(v_vs_3602_);
lean_dec_ref(v_ks_3601_);
return v___x_3604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3605_, lean_object* v_as_3606_, size_t v_i_3607_, size_t v_stop_3608_, lean_object* v_b_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_a_3616_; lean_object* v___y_3621_; uint8_t v___x_3624_; 
v___x_3624_ = lean_usize_dec_eq(v_i_3607_, v_stop_3608_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; 
v___x_3625_ = lean_array_uget_borrowed(v_as_3606_, v_i_3607_);
switch(lean_obj_tag(v___x_3625_))
{
case 0:
{
lean_object* v_key_3626_; lean_object* v_val_3627_; lean_object* v___x_3628_; 
v_key_3626_ = lean_ctor_get(v___x_3625_, 0);
v_val_3627_ = lean_ctor_get(v___x_3625_, 1);
lean_inc_ref(v_f_3605_);
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3612_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
lean_inc(v_val_3627_);
lean_inc(v_key_3626_);
v___x_3628_ = lean_apply_8(v_f_3605_, v_b_3609_, v_key_3626_, v_val_3627_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, lean_box(0));
v___y_3621_ = v___x_3628_;
goto v___jp_3620_;
}
case 1:
{
lean_object* v_node_3629_; lean_object* v___x_3630_; 
v_node_3629_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_node_3629_);
lean_inc_ref(v_f_3605_);
v___x_3630_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3605_, v_node_3629_, v_b_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3630_;
goto v___jp_3620_;
}
default: 
{
v_a_3616_ = v_b_3609_;
goto v___jp_3615_;
}
}
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_dec_ref(v_f_3605_);
v___x_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3631_, 0, v_b_3609_);
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
v___jp_3615_:
{
size_t v___x_3617_; size_t v___x_3618_; 
v___x_3617_ = ((size_t)1ULL);
v___x_3618_ = lean_usize_add(v_i_3607_, v___x_3617_);
v_i_3607_ = v___x_3618_;
v_b_3609_ = v_a_3616_;
goto _start;
}
v___jp_3620_:
{
if (lean_obj_tag(v___y_3621_) == 0)
{
lean_object* v_a_3622_; 
v_a_3622_ = lean_ctor_get(v___y_3621_, 0);
if (lean_obj_tag(v_a_3622_) == 0)
{
lean_dec_ref(v_f_3605_);
return v___y_3621_;
}
else
{
lean_object* v_a_3623_; 
lean_inc_ref(v_a_3622_);
lean_dec_ref(v___y_3621_);
v_a_3623_ = lean_ctor_get(v_a_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v_a_3622_);
v_a_3616_ = v_a_3623_;
goto v___jp_3615_;
}
}
else
{
lean_dec_ref(v_f_3605_);
return v___y_3621_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3633_, lean_object* v_as_3634_, lean_object* v_i_3635_, lean_object* v_stop_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
size_t v_i_boxed_3643_; size_t v_stop_boxed_3644_; lean_object* v_res_3645_; 
v_i_boxed_3643_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_stop_boxed_3644_ = lean_unbox_usize(v_stop_3636_);
lean_dec(v_stop_3636_);
v_res_3645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3633_, v_as_3634_, v_i_boxed_3643_, v_stop_boxed_3644_, v_b_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec_ref(v_as_3634_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3646_, v_x_3647_, v_x_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3655_, lean_object* v_s_3656_, lean_object* v_a_3657_, lean_object* v_b_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v_a_3657_);
lean_ctor_set(v___x_3664_, 1, v_b_3658_);
lean_inc(v___y_3662_);
lean_inc_ref(v___y_3661_);
lean_inc(v___y_3660_);
lean_inc_ref(v___y_3659_);
v___x_3665_ = lean_apply_7(v_f_3655_, v___x_3664_, v_s_3656_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, lean_box(0));
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3692_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3692_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3692_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
if (lean_obj_tag(v_a_3666_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3680_; 
v_a_3670_ = lean_ctor_get(v_a_3666_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_a_3666_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3672_ = v_a_3666_;
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v_a_3666_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3677_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3675_);
v___x_3677_ = v___x_3668_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3691_; 
v_a_3681_ = lean_ctor_get(v_a_3666_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_a_3666_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3683_ = v_a_3666_;
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v_a_3666_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3691_;
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
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3688_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3686_);
v___x_3688_ = v___x_3668_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
v_a_3693_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3665_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3665_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3701_, lean_object* v_s_3702_, lean_object* v_a_3703_, lean_object* v_b_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3701_, v_s_3702_, v_a_3703_, v_b_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3711_, lean_object* v_init_3712_, lean_object* v_f_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___f_3719_; lean_object* v___x_3720_; 
v___f_3719_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3719_, 0, v_f_3713_);
v___x_3720_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3719_, v_map_3711_, v_init_3712_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3729_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_a_3725_; lean_object* v___x_3727_; 
v_a_3725_ = lean_ctor_get(v_a_3721_, 0);
lean_inc(v_a_3725_);
lean_dec(v_a_3721_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v_a_3725_);
v___x_3727_ = v___x_3723_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
v_a_3730_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3720_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3720_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3738_, lean_object* v_init_3739_, lean_object* v_f_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3738_, v_init_3739_, v_f_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; lean_object* v_env_3750_; lean_object* v___x_3751_; lean_object* v_ext_3752_; lean_object* v_toEnvExtension_3753_; lean_object* v_asyncMode_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v_categories_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3749_ = lean_st_ref_get(v___y_3747_);
v_env_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc_ref_n(v_env_3750_, 2);
lean_dec(v___x_3749_);
v___x_3751_ = l_Lean_Parser_parserExtension;
v_ext_3752_ = lean_ctor_get(v___x_3751_, 1);
v_toEnvExtension_3753_ = lean_ctor_get(v_ext_3752_, 0);
v_asyncMode_3754_ = lean_ctor_get(v_toEnvExtension_3753_, 2);
v___x_3755_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3756_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3755_, v___x_3751_, v_env_3750_, v_asyncMode_3754_);
v_categories_3757_ = lean_ctor_get(v___x_3756_, 2);
lean_inc_ref(v_categories_3757_);
lean_dec(v___x_3756_);
v___x_3758_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3759_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3757_, v___x_3758_);
if (lean_obj_tag(v___x_3759_) == 1)
{
lean_object* v_val_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3797_; 
v_val_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3797_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_val_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3797_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___y_3765_; lean_object* v___x_3774_; lean_object* v_toEnvExtension_3775_; lean_object* v_exportEntriesFn_3776_; lean_object* v_asyncMode_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v_importedEntries_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v_exported_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3774_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3775_ = lean_ctor_get(v___x_3774_, 0);
v_exportEntriesFn_3776_ = lean_ctor_get(v___x_3774_, 4);
v_asyncMode_3777_ = lean_ctor_get(v_toEnvExtension_3775_, 2);
v___x_3778_ = lean_box(1);
v___x_3779_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3780_ = lean_box(0);
lean_inc_ref_n(v_env_3750_, 2);
v___x_3781_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3779_, v_toEnvExtension_3775_, v_env_3750_, v_asyncMode_3777_, v___x_3780_);
v_importedEntries_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc_ref(v_importedEntries_3782_);
lean_dec(v___x_3781_);
v___x_3783_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3778_, v___x_3774_, v_env_3750_, v_asyncMode_3777_, v___x_3780_);
lean_inc_ref(v_exportEntriesFn_3776_);
v___x_3784_ = lean_apply_2(v_exportEntriesFn_3776_, v_env_3750_, v___x_3783_);
v_exported_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_exported_3785_);
lean_dec_ref(v___x_3784_);
v___x_3786_ = lean_array_push(v_importedEntries_3782_, v_exported_3785_);
v___x_3787_ = lean_unsigned_to_nat(0u);
v___x_3788_ = lean_array_get_size(v___x_3786_);
v___x_3789_ = lean_nat_dec_lt(v___x_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_dec_ref(v___x_3786_);
v___y_3765_ = v___x_3778_;
goto v___jp_3764_;
}
else
{
uint8_t v___x_3790_; 
v___x_3790_ = lean_nat_dec_le(v___x_3788_, v___x_3788_);
if (v___x_3790_ == 0)
{
if (v___x_3789_ == 0)
{
lean_dec_ref(v___x_3786_);
v___y_3765_ = v___x_3778_;
goto v___jp_3764_;
}
else
{
size_t v___x_3791_; size_t v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = ((size_t)0ULL);
v___x_3792_ = lean_usize_of_nat(v___x_3788_);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3786_, v___x_3791_, v___x_3792_, v___x_3778_);
lean_dec_ref(v___x_3786_);
v___y_3765_ = v___x_3793_;
goto v___jp_3764_;
}
}
else
{
size_t v___x_3794_; size_t v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = ((size_t)0ULL);
v___x_3795_ = lean_usize_of_nat(v___x_3788_);
v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3786_, v___x_3794_, v___x_3795_, v___x_3778_);
lean_dec_ref(v___x_3786_);
v___y_3765_ = v___x_3796_;
goto v___jp_3764_;
}
}
v___jp_3764_:
{
lean_object* v_tables_3766_; lean_object* v_leadingTable_3767_; lean_object* v_trailingTable_3768_; lean_object* v_firstTokens_3769_; lean_object* v_firstTokens_3770_; lean_object* v___x_3772_; 
v_tables_3766_ = lean_ctor_get(v_val_3760_, 2);
v_leadingTable_3767_ = lean_ctor_get(v_tables_3766_, 0);
v_trailingTable_3768_ = lean_ctor_get(v_tables_3766_, 2);
lean_inc(v_trailingTable_3768_);
lean_inc(v_leadingTable_3767_);
lean_inc(v_val_3760_);
v_firstTokens_3769_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3760_, v_leadingTable_3767_, v___y_3765_);
v_firstTokens_3770_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3760_, v_trailingTable_3768_, v_firstTokens_3769_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set_tag(v___x_3762_, 0);
lean_ctor_set(v___x_3762_, 0, v_firstTokens_3770_);
v___x_3772_ = v___x_3762_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_firstTokens_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec(v___x_3759_);
lean_dec_ref(v_env_3750_);
v___x_3798_ = lean_box(1);
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3800_);
lean_dec(v___y_3800_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v___x_3811_; lean_object* v_env_3812_; lean_object* v___x_3813_; lean_object* v_toEnvExtension_3814_; lean_object* v_exportEntriesFn_3815_; lean_object* v_asyncMode_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v_importedEntries_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v_exported_3824_; lean_object* v___x_3825_; size_t v_sz_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
v___x_3811_ = lean_st_ref_get(v_a_3809_);
v_env_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc_ref_n(v_env_3812_, 4);
lean_dec(v___x_3811_);
v___x_3813_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3814_ = lean_ctor_get(v___x_3813_, 0);
v_exportEntriesFn_3815_ = lean_ctor_get(v___x_3813_, 4);
v_asyncMode_3816_ = lean_ctor_get(v_toEnvExtension_3814_, 2);
v___x_3817_ = lean_box(1);
v___x_3818_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3819_ = lean_box(0);
v___x_3820_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3818_, v_toEnvExtension_3814_, v_env_3812_, v_asyncMode_3816_, v___x_3819_);
v_importedEntries_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc_ref(v_importedEntries_3821_);
lean_dec(v___x_3820_);
v___x_3822_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3817_, v___x_3813_, v_env_3812_, v_asyncMode_3816_, v___x_3819_);
lean_inc_ref(v_exportEntriesFn_3815_);
v___x_3823_ = lean_apply_2(v_exportEntriesFn_3815_, v_env_3812_, v___x_3822_);
v_exported_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_exported_3824_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = lean_array_push(v_importedEntries_3821_, v_exported_3824_);
v_sz_3826_ = lean_array_size(v___x_3825_);
v___x_3827_ = ((size_t)0ULL);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3825_, v_sz_3826_, v___x_3827_, v___x_3817_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
lean_dec_ref(v___x_3825_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3853_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3853_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3853_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3833_; lean_object* v_ext_3834_; lean_object* v_toEnvExtension_3835_; lean_object* v_asyncMode_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v_categories_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3833_ = l_Lean_Parser_parserExtension;
v_ext_3834_ = lean_ctor_get(v___x_3833_, 1);
v_toEnvExtension_3835_ = lean_ctor_get(v_ext_3834_, 0);
v_asyncMode_3836_ = lean_ctor_get(v_toEnvExtension_3835_, 2);
v___x_3837_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3812_);
v___x_3838_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3837_, v___x_3833_, v_env_3812_, v_asyncMode_3836_);
v_categories_3839_ = lean_ctor_get(v___x_3838_, 2);
lean_inc_ref(v_categories_3839_);
lean_dec(v___x_3838_);
v___x_3840_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3841_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3842_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3839_, v___x_3841_);
if (lean_obj_tag(v___x_3842_) == 1)
{
lean_object* v_val_3843_; lean_object* v___x_3844_; lean_object* v_a_3845_; lean_object* v_kinds_3846_; lean_object* v___x_3847_; lean_object* v___f_3848_; lean_object* v___x_3849_; 
lean_del_object(v___x_3831_);
v_val_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_val_3843_);
lean_dec_ref(v___x_3842_);
v___x_3844_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3809_);
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
v_kinds_3846_ = lean_ctor_get(v_val_3843_, 1);
lean_inc_ref(v_kinds_3846_);
lean_dec(v_val_3843_);
v___x_3847_ = lean_box(v_includeUnnamed_3805_);
v___f_3848_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3848_, 0, v_env_3812_);
lean_closure_set(v___f_3848_, 1, v_a_3829_);
lean_closure_set(v___f_3848_, 2, v_a_3845_);
lean_closure_set(v___f_3848_, 3, v___x_3847_);
v___x_3849_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3846_, v___x_3840_, v___f_3848_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
return v___x_3849_;
}
else
{
lean_object* v___x_3851_; 
lean_dec(v___x_3842_);
lean_dec(v_a_3829_);
lean_dec_ref(v_env_3812_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v___x_3840_);
v___x_3851_ = v___x_3831_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3840_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec_ref(v_env_3812_);
v_a_3854_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3828_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3828_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
uint8_t v_includeUnnamed_boxed_3868_; lean_object* v_res_3869_; 
v_includeUnnamed_boxed_3868_ = lean_unbox(v_includeUnnamed_3862_);
v_res_3869_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3868_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3870_, size_t v_sz_3871_, size_t v_i_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3870_, v_sz_3871_, v_i_3872_, v_b_3873_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3880_, lean_object* v_sz_3881_, lean_object* v_i_3882_, lean_object* v_b_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
size_t v_sz_boxed_3889_; size_t v_i_boxed_3890_; lean_object* v_res_3891_; 
v_sz_boxed_3889_ = lean_unbox_usize(v_sz_3881_);
lean_dec(v_sz_3881_);
v_i_boxed_3890_ = lean_unbox_usize(v_i_3882_);
lean_dec(v_i_3882_);
v_res_3891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3880_, v_sz_boxed_3889_, v_i_boxed_3890_, v_b_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec_ref(v_as_3880_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3904_, lean_object* v_00_u03b2_3905_, lean_object* v_map_3906_, lean_object* v_init_3907_, lean_object* v_f_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3906_, v_init_3907_, v_f_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3915_, lean_object* v_00_u03b2_3916_, lean_object* v_map_3917_, lean_object* v_init_3918_, lean_object* v_f_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3915_, v_00_u03b2_3916_, v_map_3917_, v_init_3918_, v_f_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3926_, lean_object* v_f_3927_, lean_object* v_init_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3927_, v_map_3926_, v_init_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3935_, lean_object* v_f_3936_, lean_object* v_init_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3935_, v_f_3936_, v_init_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3944_, lean_object* v_00_u03c3_3945_, lean_object* v_00_u03b2_3946_, lean_object* v_map_3947_, lean_object* v_f_3948_, lean_object* v_init_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3948_, v_map_3947_, v_init_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3956_, lean_object* v_00_u03c3_3957_, lean_object* v_00_u03b2_3958_, lean_object* v_map_3959_, lean_object* v_f_3960_, lean_object* v_init_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3956_, v_00_u03c3_3957_, v_00_u03b2_3958_, v_map_3959_, v_f_3960_, v_init_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3968_, lean_object* v_00_u03c3_3969_, lean_object* v_00_u03b1_3970_, lean_object* v_00_u03b2_3971_, lean_object* v_f_3972_, lean_object* v_x_3973_, lean_object* v_x_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3972_, v_x_3973_, v_x_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3981_, lean_object* v_00_u03c3_3982_, lean_object* v_00_u03b1_3983_, lean_object* v_00_u03b2_3984_, lean_object* v_f_3985_, lean_object* v_x_3986_, lean_object* v_x_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3981_, v_00_u03c3_3982_, v_00_u03b1_3983_, v_00_u03b2_3984_, v_f_3985_, v_x_3986_, v_x_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3994_, lean_object* v_00_u03b2_3995_, lean_object* v_00_u03c3_3996_, lean_object* v_00_u03c3_3997_, lean_object* v_f_3998_, lean_object* v_as_3999_, size_t v_i_4000_, size_t v_stop_4001_, lean_object* v_b_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3998_, v_as_3999_, v_i_4000_, v_stop_4001_, v_b_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4009_, lean_object* v_00_u03b2_4010_, lean_object* v_00_u03c3_4011_, lean_object* v_00_u03c3_4012_, lean_object* v_f_4013_, lean_object* v_as_4014_, lean_object* v_i_4015_, lean_object* v_stop_4016_, lean_object* v_b_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
size_t v_i_boxed_4023_; size_t v_stop_boxed_4024_; lean_object* v_res_4025_; 
v_i_boxed_4023_ = lean_unbox_usize(v_i_4015_);
lean_dec(v_i_4015_);
v_stop_boxed_4024_ = lean_unbox_usize(v_stop_4016_);
lean_dec(v_stop_4016_);
v_res_4025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_4009_, v_00_u03b2_4010_, v_00_u03c3_4011_, v_00_u03c3_4012_, v_f_4013_, v_as_4014_, v_i_boxed_4023_, v_stop_boxed_4024_, v_b_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec_ref(v_as_4014_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_4026_, lean_object* v_00_u03c3_4027_, lean_object* v_00_u03b1_4028_, lean_object* v_00_u03b2_4029_, lean_object* v_f_4030_, lean_object* v_keys_4031_, lean_object* v_vals_4032_, lean_object* v_heq_4033_, lean_object* v_i_4034_, lean_object* v_acc_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4030_, v_keys_4031_, v_vals_4032_, v_i_4034_, v_acc_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_4042_, lean_object* v_00_u03c3_4043_, lean_object* v_00_u03b1_4044_, lean_object* v_00_u03b2_4045_, lean_object* v_f_4046_, lean_object* v_keys_4047_, lean_object* v_vals_4048_, lean_object* v_heq_4049_, lean_object* v_i_4050_, lean_object* v_acc_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_4042_, v_00_u03c3_4043_, v_00_u03b1_4044_, v_00_u03b2_4045_, v_f_4046_, v_keys_4047_, v_vals_4048_, v_heq_4049_, v_i_4050_, v_acc_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec_ref(v_vals_4048_);
lean_dec_ref(v_keys_4047_);
return v_res_4057_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Doc(builtin);
}
#ifdef __cplusplus
}
#endif
