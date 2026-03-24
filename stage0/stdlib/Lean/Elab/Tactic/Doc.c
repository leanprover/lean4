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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Displays all available tactic tags, with documentation.\n"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
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
v___x_26_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
lean_ctor_set(v___x_26_, 3, v___x_24_);
lean_ctor_set(v___x_26_, 4, v___x_24_);
lean_ctor_set(v___x_26_, 5, v___x_24_);
lean_ctor_set(v___x_26_, 6, v___x_24_);
lean_ctor_set(v___x_26_, 7, v___x_24_);
lean_ctor_set(v___x_26_, 8, v___x_24_);
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
lean_inc(v_macroStack_153_);
lean_dec_ref(v___y_148_);
v___x_154_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_147_, v___y_149_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
lean_inc(v_macroStack_153_);
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
lean_dec_ref(v___y_148_);
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
lean_inc_ref(v_a_248_);
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
lean_inc_ref(v_a_248_);
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
lean_inc_ref(v_a_248_);
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
lean_inc_ref(v_a_248_);
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
lean_inc_ref(v_toEnvExtension_298_);
v_asyncMode_299_ = lean_ctor_get(v_toEnvExtension_298_, 2);
lean_inc(v_asyncMode_299_);
lean_dec_ref(v_toEnvExtension_298_);
v___x_300_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_a_276_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_297_, v_env_283_, v___x_301_, v_asyncMode_299_, v___x_302_);
lean_dec(v_asyncMode_299_);
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
lean_inc_ref(v___y_372_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_419_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_421_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_422_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_423_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_419_, v___x_420_, v___x_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_453_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_454_ = l_Lean_addBuiltinDeclarationRanges(v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
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
lean_dec(v_pre_485_);
lean_dec_ref(v_pre_484_);
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
lean_inc_ref(v_a_525_);
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
lean_inc_ref(v_a_525_);
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
lean_inc_ref(v_a_525_);
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
lean_inc_ref(v_toEnvExtension_549_);
v_asyncMode_550_ = lean_ctor_get(v_toEnvExtension_549_, 2);
lean_inc(v_asyncMode_550_);
lean_dec_ref(v_toEnvExtension_549_);
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
lean_dec(v_asyncMode_550_);
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
lean_inc_ref(v___y_566_);
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
lean_inc_ref(v___y_566_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_631_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_632_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_634_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_630_, v___x_631_, v___x_632_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_664_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_665_ = l_Lean_addBuiltinDeclarationRanges(v___x_663_, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
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
v___x_880_ = lean_nat_add(v___y_877_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v___y_877_);
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
lean_ctor_set(v___x_884_, 3, v___y_878_);
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
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___y_878_);
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
v___y_877_ = v___x_902_;
v___y_878_ = v___x_901_;
v___y_879_ = v_size_903_;
goto v___jp_876_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___y_877_ = v___x_902_;
v___y_878_ = v___x_901_;
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
lean_inc_ref(v_es_1037_);
lean_dec_ref(v_x_1034_);
v___x_1038_ = lean_box(2);
v___x_1039_ = ((size_t)5ULL);
v___x_1040_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1041_ = lean_usize_land(v_x_1035_, v___x_1040_);
v_j_1042_ = lean_usize_to_nat(v___x_1041_);
v___x_1043_ = lean_array_get(v___x_1038_, v_es_1037_, v_j_1042_);
lean_dec(v_j_1042_);
lean_dec_ref(v_es_1037_);
switch(lean_obj_tag(v___x_1043_))
{
case 0:
{
lean_object* v_key_1044_; uint8_t v___x_1045_; 
v_key_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_key_1044_);
lean_dec_ref(v___x_1043_);
v___x_1045_ = lean_name_eq(v_x_1036_, v_key_1044_);
lean_dec(v_key_1044_);
return v___x_1045_;
}
case 1:
{
lean_object* v_node_1046_; size_t v___x_1047_; 
v_node_1046_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_node_1046_);
lean_dec_ref(v___x_1043_);
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
lean_inc_ref(v_ks_1050_);
lean_dec_ref(v_x_1034_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1050_, v___x_1051_, v_x_1036_);
lean_dec_ref(v_ks_1050_);
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
lean_inc_ref(v_kinds_1079_);
lean_dec_ref(v_tactics_1073_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v_toPure_1420_, lean_object* v___x_1421_, lean_object* v___f_1422_, lean_object* v_env_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v_ext_1425_; lean_object* v_toEnvExtension_1426_; lean_object* v_asyncMode_1427_; lean_object* v___x_1428_; lean_object* v_categories_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1424_ = l_Lean_Parser_parserExtension;
v_ext_1425_ = lean_ctor_get(v___x_1424_, 1);
lean_inc_ref(v_ext_1425_);
v_toEnvExtension_1426_ = lean_ctor_get(v_ext_1425_, 0);
lean_inc_ref(v_toEnvExtension_1426_);
lean_dec_ref(v_ext_1425_);
v_asyncMode_1427_ = lean_ctor_get(v_toEnvExtension_1426_, 2);
lean_inc(v_asyncMode_1427_);
lean_dec_ref(v_toEnvExtension_1426_);
lean_inc_ref(v_env_1423_);
v___x_1428_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1416_, v___x_1424_, v_env_1423_, v_asyncMode_1427_);
lean_dec(v_asyncMode_1427_);
v_categories_1429_ = lean_ctor_get(v___x_1428_, 2);
lean_inc_ref(v_categories_1429_);
lean_dec(v___x_1428_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1431_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1417_, v___x_1418_, v_categories_1429_, v___x_1430_);
if (lean_obj_tag(v___x_1431_) == 1)
{
lean_object* v_val_1432_; lean_object* v___y_1434_; lean_object* v___x_1441_; lean_object* v_toEnvExtension_1442_; lean_object* v_exportEntriesFn_1443_; lean_object* v_asyncMode_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_importedEntries_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v_val_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1432_);
lean_dec_ref(v___x_1431_);
v___x_1441_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc_ref(v_toEnvExtension_1442_);
v_exportEntriesFn_1443_ = lean_ctor_get(v___x_1441_, 4);
lean_inc_ref(v_exportEntriesFn_1443_);
v_asyncMode_1444_ = lean_ctor_get(v_toEnvExtension_1442_, 2);
lean_inc(v_asyncMode_1444_);
v___x_1445_ = lean_box(0);
lean_inc_ref(v_env_1423_);
v___x_1446_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1419_, v_toEnvExtension_1442_, v_env_1423_, v_asyncMode_1444_, v___x_1445_);
lean_dec_ref(v_toEnvExtension_1442_);
v_importedEntries_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_importedEntries_1447_);
lean_dec(v___x_1446_);
v___x_1448_ = lean_box(1);
lean_inc_ref(v_env_1423_);
v___x_1449_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1421_, v___x_1441_, v_env_1423_, v_asyncMode_1444_, v___x_1445_);
lean_dec(v_asyncMode_1444_);
v___x_1450_ = 0;
v___x_1451_ = lean_box(v___x_1450_);
v___x_1452_ = lean_apply_3(v_exportEntriesFn_1443_, v_env_1423_, v___x_1449_, v___x_1451_);
v___x_1453_ = lean_array_push(v_importedEntries_1447_, v___x_1452_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_array_get_size(v___x_1453_);
v___x_1456_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1457_ = lean_nat_dec_lt(v___x_1454_, v___x_1455_);
if (v___x_1457_ == 0)
{
lean_dec_ref(v___x_1453_);
lean_dec_ref(v___f_1422_);
v___y_1434_ = v___x_1448_;
goto v___jp_1433_;
}
else
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_nat_dec_le(v___x_1455_, v___x_1455_);
if (v___x_1458_ == 0)
{
if (v___x_1457_ == 0)
{
lean_dec_ref(v___x_1453_);
lean_dec_ref(v___f_1422_);
v___y_1434_ = v___x_1448_;
goto v___jp_1433_;
}
else
{
size_t v___x_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = ((size_t)0ULL);
v___x_1460_ = lean_usize_of_nat(v___x_1455_);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1456_, v___f_1422_, v___x_1453_, v___x_1459_, v___x_1460_, v___x_1448_);
v___y_1434_ = v___x_1461_;
goto v___jp_1433_;
}
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = lean_usize_of_nat(v___x_1455_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1456_, v___f_1422_, v___x_1453_, v___x_1462_, v___x_1463_, v___x_1448_);
v___y_1434_ = v___x_1464_;
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
v___x_1440_ = lean_apply_2(v_toPure_1420_, lean_box(0), v_firstTokens_1439_);
return v___x_1440_;
}
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_dec(v___x_1431_);
lean_dec_ref(v_env_1423_);
lean_dec_ref(v___f_1422_);
lean_dec(v___x_1421_);
lean_dec_ref(v___x_1419_);
v___x_1465_ = lean_box(1);
v___x_1466_ = lean_apply_2(v_toPure_1420_, lean_box(0), v___x_1465_);
return v___x_1466_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_box(1);
v___x_1471_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1474_, lean_object* v_inst_1475_){
_start:
{
lean_object* v_toApplicative_1476_; lean_object* v_toBind_1477_; lean_object* v_getEnv_1478_; lean_object* v_toPure_1479_; lean_object* v___f_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; 
v_toApplicative_1476_ = lean_ctor_get(v_inst_1474_, 0);
lean_inc_ref(v_toApplicative_1476_);
v_toBind_1477_ = lean_ctor_get(v_inst_1474_, 1);
lean_inc(v_toBind_1477_);
lean_dec_ref(v_inst_1474_);
v_getEnv_1478_ = lean_ctor_get(v_inst_1475_, 0);
lean_inc(v_getEnv_1478_);
lean_dec_ref(v_inst_1475_);
v_toPure_1479_ = lean_ctor_get(v_toApplicative_1476_, 1);
lean_inc(v_toPure_1479_);
lean_dec_ref(v_toApplicative_1476_);
v___f_1480_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1481_ = lean_box(1);
v___x_1482_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1483_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1484_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1485_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1486_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2), 8, 7);
lean_closure_set(v___f_1486_, 0, v___x_1485_);
lean_closure_set(v___f_1486_, 1, v___x_1483_);
lean_closure_set(v___f_1486_, 2, v___x_1484_);
lean_closure_set(v___f_1486_, 3, v___x_1482_);
lean_closure_set(v___f_1486_, 4, v_toPure_1479_);
lean_closure_set(v___f_1486_, 5, v___x_1481_);
lean_closure_set(v___f_1486_, 6, v___f_1480_);
v___x_1487_ = lean_apply_4(v_toBind_1477_, lean_box(0), lean_box(0), v_getEnv_1478_, v___f_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1488_, lean_object* v_inst_1489_, lean_object* v_inst_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1489_, v_inst_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_x_1492_, lean_object* v_y_1493_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_nat_dec_lt(v_x_1492_, v_y_1493_);
if (v___x_1494_ == 0)
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_nat_dec_eq(v_x_1492_, v_y_1493_);
if (v___x_1495_ == 0)
{
uint8_t v___x_1496_; 
v___x_1496_ = 2;
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = 1;
return v___x_1497_;
}
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = 0;
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed(lean_object* v_x_1499_, lean_object* v_y_1500_){
_start:
{
uint8_t v_res_1501_; lean_object* v_r_1502_; 
v_res_1501_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(v_x_1499_, v_y_1500_);
lean_dec(v_y_1500_);
lean_dec(v_x_1499_);
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v___f_1503_, lean_object* v_a_1504_, lean_object* v_x_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_fst_1507_; lean_object* v_snd_1508_; lean_object* v_r_1509_; lean_object* v___x_1510_; 
v_fst_1507_ = lean_ctor_get(v_a_1504_, 0);
lean_inc(v_fst_1507_);
v_snd_1508_ = lean_ctor_get(v_a_1504_, 1);
lean_inc(v_snd_1508_);
lean_dec_ref(v_a_1504_);
v_r_1509_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_1503_, v_fst_1507_, v_snd_1508_, v___y_1506_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_r_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2(lean_object* v_n_1517_, lean_object* v___y_1518_, lean_object* v___f_1519_, lean_object* v_toPure_1520_, lean_object* v_firsts_1521_, lean_object* v_____do__lift_1522_){
_start:
{
lean_object* v___y_1524_; lean_object* v_val_1556_; 
if (lean_obj_tag(v_____do__lift_1522_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3));
lean_inc(v_n_1517_);
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1558_, v_firsts_1521_, v_n_1517_);
if (lean_obj_tag(v___x_1559_) == 0)
{
uint8_t v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = 1;
lean_inc(v_n_1517_);
v___x_1561_ = l_Lean_Name_toString(v_n_1517_, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
v___y_1524_ = v___x_1562_;
goto v___jp_1523_;
}
else
{
lean_object* v_val_1563_; 
v_val_1563_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1563_);
lean_dec_ref(v___x_1559_);
v_val_1556_ = v_val_1563_;
goto v___jp_1555_;
}
}
else
{
lean_object* v_val_1564_; 
lean_dec(v_firsts_1521_);
v_val_1564_ = lean_ctor_get(v_____do__lift_1522_, 0);
lean_inc(v_val_1564_);
lean_dec_ref(v_____do__lift_1522_);
v_val_1556_ = v_val_1564_;
goto v___jp_1555_;
}
v___jp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_r_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___y_1524_);
v___x_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___x_1525_);
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_1531_ = lean_box(2);
v___x_1532_ = 1;
lean_inc(v_n_1517_);
v___x_1533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1517_, v___x_1532_);
v___x_1534_ = lean_string_utf8_byte_size(v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1526_);
lean_ctor_set(v___x_1535_, 2, v___x_1534_);
v___x_1536_ = lean_box(0);
lean_inc(v_n_1517_);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_n_1517_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1536_);
lean_inc(v_n_1517_);
v___x_1539_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1531_);
lean_ctor_set(v___x_1539_, 1, v___x_1535_);
lean_ctor_set(v___x_1539_, 2, v_n_1517_);
lean_ctor_set(v___x_1539_, 3, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1530_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_LocalContext_empty;
v___x_1542_ = lean_box(0);
v___x_1543_ = l_Lean_Expr_const___override(v_n_1517_, v___y_1518_);
v___x_1544_ = 0;
v___x_1545_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1545_, 0, v___x_1540_);
lean_ctor_set(v___x_1545_, 1, v___x_1541_);
lean_ctor_set(v___x_1545_, 2, v___x_1542_);
lean_ctor_set(v___x_1545_, 3, v___x_1543_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*4, v___x_1544_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*4 + 1, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1526_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___x_1536_);
v___x_1549_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v_r_1550_ = lean_box(1);
v___x_1551_ = l_List_forIn_x27_loop___redArg(v___x_1549_, v___f_1519_, v___x_1548_, v_r_1550_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1529_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = lean_apply_2(v_toPure_1520_, lean_box(0), v___x_1553_);
return v___x_1554_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_val_1556_);
v___y_1524_ = v___x_1557_;
goto v___jp_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3(lean_object* v_n_1565_, lean_object* v___f_1566_, lean_object* v_toPure_1567_, lean_object* v_firsts_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_toBind_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, lean_object* v___f_1574_, lean_object* v_env_1575_){
_start:
{
lean_object* v___y_1577_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = l_Lean_Environment_constants(v_env_1575_);
lean_inc(v_n_1565_);
v___x_1582_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1572_, v___x_1573_, v___x_1581_, v_n_1565_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref(v___f_1574_);
v___x_1583_ = lean_box(0);
v___y_1577_ = v___x_1583_;
goto v___jp_1576_;
}
else
{
lean_object* v_val_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_val_1584_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1584_);
lean_dec_ref(v___x_1582_);
v___x_1585_ = l_Lean_ConstantInfo_levelParams(v_val_1584_);
lean_dec(v_val_1584_);
v___x_1586_ = lean_box(0);
v___x_1587_ = l_List_mapTR_loop___redArg(v___f_1574_, v___x_1585_, v___x_1586_);
v___y_1577_ = v___x_1587_;
goto v___jp_1576_;
}
v___jp_1576_:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_inc(v_n_1565_);
v___f_1578_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1578_, 0, v_n_1565_);
lean_closure_set(v___f_1578_, 1, v___y_1577_);
lean_closure_set(v___f_1578_, 2, v___f_1566_);
lean_closure_set(v___f_1578_, 3, v_toPure_1567_);
lean_closure_set(v___f_1578_, 4, v_firsts_1568_);
v___x_1579_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1569_, v_inst_1570_, v_n_1565_);
v___x_1580_ = lean_apply_4(v_toBind_1571_, lean_box(0), lean_box(0), v___x_1579_, v___f_1578_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_firsts_1594_, lean_object* v_n_1595_){
_start:
{
lean_object* v_toApplicative_1596_; lean_object* v_toBind_1597_; lean_object* v_getEnv_1598_; lean_object* v_toPure_1599_; lean_object* v___f_1600_; lean_object* v___f_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; 
v_toApplicative_1596_ = lean_ctor_get(v_inst_1592_, 0);
v_toBind_1597_ = lean_ctor_get(v_inst_1592_, 1);
lean_inc(v_toBind_1597_);
v_getEnv_1598_ = lean_ctor_get(v_inst_1593_, 0);
lean_inc(v_getEnv_1598_);
v_toPure_1599_ = lean_ctor_get(v_toApplicative_1596_, 1);
lean_inc(v_toPure_1599_);
v___f_1600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1));
v___f_1601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2));
v___x_1602_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1603_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
lean_inc(v_toBind_1597_);
v___f_1604_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3), 11, 10);
lean_closure_set(v___f_1604_, 0, v_n_1595_);
lean_closure_set(v___f_1604_, 1, v___f_1600_);
lean_closure_set(v___f_1604_, 2, v_toPure_1599_);
lean_closure_set(v___f_1604_, 3, v_firsts_1594_);
lean_closure_set(v___f_1604_, 4, v_inst_1592_);
lean_closure_set(v___f_1604_, 5, v_inst_1593_);
lean_closure_set(v___f_1604_, 6, v_toBind_1597_);
lean_closure_set(v___f_1604_, 7, v___x_1602_);
lean_closure_set(v___f_1604_, 8, v___x_1603_);
lean_closure_set(v___f_1604_, 9, v___f_1601_);
v___x_1605_ = lean_apply_4(v_toBind_1597_, lean_box(0), lean_box(0), v_getEnv_1598_, v___f_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_firsts_1609_, lean_object* v_n_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1607_, v_inst_1608_, v_firsts_1609_, v_n_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1616_);
lean_dec_ref(v_s_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1618_, lean_object* v_x1_1619_, lean_object* v_x2_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1621_ = l_Lean_Name_toString(v_x1_1619_, v___x_1618_);
v___x_1622_ = l_Lean_Name_toString(v_x2_1620_, v___x_1618_);
v___x_1623_ = lean_string_dec_lt(v___x_1621_, v___x_1622_);
lean_dec_ref(v___x_1622_);
lean_dec_ref(v___x_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1624_, lean_object* v_x1_1625_, lean_object* v_x2_1626_){
_start:
{
uint8_t v___x_18064__boxed_1627_; uint8_t v_res_1628_; lean_object* v_r_1629_; 
v___x_18064__boxed_1627_ = lean_unbox(v___x_1624_);
v_res_1628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_18064__boxed_1627_, v_x1_1625_, v_x2_1626_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_as_1630_, lean_object* v_lo_1631_, lean_object* v_hi_1632_){
_start:
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_nat_dec_lt(v_lo_1631_, v_hi_1632_);
if (v___x_1633_ == 0)
{
lean_dec(v_lo_1631_);
return v_as_1630_;
}
else
{
lean_object* v___x_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v_fst_1637_; lean_object* v_snd_1638_; uint8_t v___x_1639_; 
v___x_1634_ = lean_box(v___x_1633_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1635_, 0, v___x_1634_);
lean_inc(v_lo_1631_);
v___x_1636_ = l_Array_qpartition___redArg(v_as_1630_, v___f_1635_, v_lo_1631_, v_hi_1632_);
v_fst_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_fst_1637_);
v_snd_1638_ = lean_ctor_get(v___x_1636_, 1);
lean_inc(v_snd_1638_);
lean_dec_ref(v___x_1636_);
v___x_1639_ = lean_nat_dec_le(v_hi_1632_, v_fst_1637_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_snd_1638_, v_lo_1631_, v_fst_1637_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_nat_add(v_fst_1637_, v___x_1641_);
lean_dec(v_fst_1637_);
v_as_1630_ = v___x_1640_;
v_lo_1631_ = v___x_1642_;
goto _start;
}
else
{
lean_dec(v_fst_1637_);
lean_dec(v_lo_1631_);
return v_snd_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_as_1644_, lean_object* v_lo_1645_, lean_object* v_hi_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_as_1644_, v_lo_1645_, v_hi_1646_);
lean_dec(v_hi_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(lean_object* v_a_1648_, lean_object* v_x_1649_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_box(0);
return v___x_1650_;
}
else
{
lean_object* v_key_1651_; lean_object* v_value_1652_; lean_object* v_tail_1653_; uint8_t v___x_1654_; 
v_key_1651_ = lean_ctor_get(v_x_1649_, 0);
v_value_1652_ = lean_ctor_get(v_x_1649_, 1);
v_tail_1653_ = lean_ctor_get(v_x_1649_, 2);
v___x_1654_ = lean_name_eq(v_key_1651_, v_a_1648_);
if (v___x_1654_ == 0)
{
v_x_1649_ = v_tail_1653_;
goto _start;
}
else
{
lean_object* v___x_1656_; 
lean_inc(v_value_1652_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_value_1652_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg___boxed(lean_object* v_a_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec(v_a_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(lean_object* v_m_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_buckets_1662_; lean_object* v___x_1663_; uint64_t v___y_1665_; 
v_buckets_1662_ = lean_ctor_get(v_m_1660_, 1);
v___x_1663_ = lean_array_get_size(v_buckets_1662_);
if (lean_obj_tag(v_a_1661_) == 0)
{
uint64_t v___x_1679_; 
v___x_1679_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1665_ = v___x_1679_;
goto v___jp_1664_;
}
else
{
uint64_t v_hash_1680_; 
v_hash_1680_ = lean_ctor_get_uint64(v_a_1661_, sizeof(void*)*2);
v___y_1665_ = v_hash_1680_;
goto v___jp_1664_;
}
v___jp_1664_:
{
uint64_t v___x_1666_; uint64_t v___x_1667_; uint64_t v_fold_1668_; uint64_t v___x_1669_; uint64_t v___x_1670_; uint64_t v___x_1671_; size_t v___x_1672_; size_t v___x_1673_; size_t v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1666_ = 32ULL;
v___x_1667_ = lean_uint64_shift_right(v___y_1665_, v___x_1666_);
v_fold_1668_ = lean_uint64_xor(v___y_1665_, v___x_1667_);
v___x_1669_ = 16ULL;
v___x_1670_ = lean_uint64_shift_right(v_fold_1668_, v___x_1669_);
v___x_1671_ = lean_uint64_xor(v_fold_1668_, v___x_1670_);
v___x_1672_ = lean_uint64_to_usize(v___x_1671_);
v___x_1673_ = lean_usize_of_nat(v___x_1663_);
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_sub(v___x_1673_, v___x_1674_);
v___x_1676_ = lean_usize_land(v___x_1672_, v___x_1675_);
v___x_1677_ = lean_array_uget_borrowed(v_buckets_1662_, v___x_1676_);
v___x_1678_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1661_, v___x_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg___boxed(lean_object* v_m_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_m_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1684_, lean_object* v_vals_1685_, lean_object* v_i_1686_, lean_object* v_k_1687_){
_start:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = lean_array_get_size(v_keys_1684_);
v___x_1689_ = lean_nat_dec_lt(v_i_1686_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_dec(v_i_1686_);
v___x_1690_ = lean_box(0);
return v___x_1690_;
}
else
{
lean_object* v_k_x27_1691_; uint8_t v___x_1692_; 
v_k_x27_1691_ = lean_array_fget_borrowed(v_keys_1684_, v_i_1686_);
v___x_1692_ = lean_name_eq(v_k_1687_, v_k_x27_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_nat_add(v_i_1686_, v___x_1693_);
lean_dec(v_i_1686_);
v_i_1686_ = v___x_1694_;
goto _start;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_array_fget_borrowed(v_vals_1685_, v_i_1686_);
lean_dec(v_i_1686_);
lean_inc(v___x_1696_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1698_, lean_object* v_vals_1699_, lean_object* v_i_1700_, lean_object* v_k_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1698_, v_vals_1699_, v_i_1700_, v_k_1701_);
lean_dec(v_k_1701_);
lean_dec_ref(v_vals_1699_);
lean_dec_ref(v_keys_1698_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1703_, size_t v_x_1704_, lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v_es_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1727_; 
v_es_1706_ = lean_ctor_get(v_x_1703_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_x_1703_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1708_ = v_x_1703_;
v_isShared_1709_ = v_isSharedCheck_1727_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_es_1706_);
lean_dec(v_x_1703_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1727_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v_j_1714_; lean_object* v___x_1715_; 
v___x_1710_ = lean_box(2);
v___x_1711_ = ((size_t)5ULL);
v___x_1712_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1713_ = lean_usize_land(v_x_1704_, v___x_1712_);
v_j_1714_ = lean_usize_to_nat(v___x_1713_);
v___x_1715_ = lean_array_get(v___x_1710_, v_es_1706_, v_j_1714_);
lean_dec(v_j_1714_);
lean_dec_ref(v_es_1706_);
switch(lean_obj_tag(v___x_1715_))
{
case 0:
{
lean_object* v_key_1716_; lean_object* v_val_1717_; uint8_t v___x_1718_; 
v_key_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_key_1716_);
v_val_1717_ = lean_ctor_get(v___x_1715_, 1);
lean_inc(v_val_1717_);
lean_dec_ref(v___x_1715_);
v___x_1718_ = lean_name_eq(v_x_1705_, v_key_1716_);
lean_dec(v_key_1716_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_dec(v_val_1717_);
lean_del_object(v___x_1708_);
v___x_1719_ = lean_box(0);
return v___x_1719_;
}
else
{
lean_object* v___x_1721_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 1);
lean_ctor_set(v___x_1708_, 0, v_val_1717_);
v___x_1721_ = v___x_1708_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_val_1717_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
case 1:
{
lean_object* v_node_1723_; size_t v___x_1724_; 
lean_del_object(v___x_1708_);
v_node_1723_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_node_1723_);
lean_dec_ref(v___x_1715_);
v___x_1724_ = lean_usize_shift_right(v_x_1704_, v___x_1711_);
v_x_1703_ = v_node_1723_;
v_x_1704_ = v___x_1724_;
goto _start;
}
default: 
{
lean_object* v___x_1726_; 
lean_del_object(v___x_1708_);
v___x_1726_ = lean_box(0);
return v___x_1726_;
}
}
}
}
else
{
lean_object* v_ks_1728_; lean_object* v_vs_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_ks_1728_ = lean_ctor_get(v_x_1703_, 0);
lean_inc_ref(v_ks_1728_);
v_vs_1729_ = lean_ctor_get(v_x_1703_, 1);
lean_inc_ref(v_vs_1729_);
lean_dec_ref(v_x_1703_);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1728_, v_vs_1729_, v___x_1730_, v_x_1705_);
lean_dec_ref(v_vs_1729_);
lean_dec_ref(v_ks_1728_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_x_1734_){
_start:
{
size_t v_x_18181__boxed_1735_; lean_object* v_res_1736_; 
v_x_18181__boxed_1735_ = lean_unbox_usize(v_x_1733_);
lean_dec(v_x_1733_);
v_res_1736_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1732_, v_x_18181__boxed_1735_, v_x_1734_);
lean_dec(v_x_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
uint64_t v___y_1740_; 
if (lean_obj_tag(v_x_1738_) == 0)
{
uint64_t v___x_1743_; 
v___x_1743_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1740_ = v___x_1743_;
goto v___jp_1739_;
}
else
{
uint64_t v_hash_1744_; 
v_hash_1744_ = lean_ctor_get_uint64(v_x_1738_, sizeof(void*)*2);
v___y_1740_ = v_hash_1744_;
goto v___jp_1739_;
}
v___jp_1739_:
{
size_t v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_uint64_to_usize(v___y_1740_);
v___x_1742_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1737_, v___x_1741_, v_x_1738_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1745_, v_x_1746_);
lean_dec(v_x_1746_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
uint8_t v_stage_u2081_1750_; 
v_stage_u2081_1750_ = lean_ctor_get_uint8(v_x_1748_, sizeof(void*)*2);
if (v_stage_u2081_1750_ == 0)
{
lean_object* v_map_u2081_1751_; lean_object* v_map_u2082_1752_; lean_object* v___x_1753_; 
v_map_u2081_1751_ = lean_ctor_get(v_x_1748_, 0);
lean_inc_ref(v_map_u2081_1751_);
v_map_u2082_1752_ = lean_ctor_get(v_x_1748_, 1);
lean_inc_ref(v_map_u2082_1752_);
lean_dec_ref(v_x_1748_);
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1751_, v_x_1749_);
lean_dec_ref(v_map_u2081_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1752_, v_x_1749_);
return v___x_1754_;
}
else
{
lean_dec_ref(v_map_u2082_1752_);
return v___x_1753_;
}
}
else
{
lean_object* v_map_u2081_1755_; lean_object* v___x_1756_; 
v_map_u2081_1755_ = lean_ctor_get(v_x_1748_, 0);
lean_inc_ref(v_map_u2081_1755_);
lean_dec_ref(v_x_1748_);
v___x_1756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1755_, v_x_1749_);
lean_dec_ref(v_map_u2081_1755_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg___boxed(lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_1757_, v_x_1758_);
lean_dec(v_x_1758_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
if (lean_obj_tag(v_a_1760_) == 0)
{
lean_object* v___x_1762_; 
v___x_1762_ = l_List_reverse___redArg(v_a_1761_);
return v___x_1762_;
}
else
{
lean_object* v_head_1763_; lean_object* v_tail_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1773_; 
v_head_1763_ = lean_ctor_get(v_a_1760_, 0);
v_tail_1764_ = lean_ctor_get(v_a_1760_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_a_1760_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1766_ = v_a_1760_;
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_tail_1764_);
lean_inc(v_head_1763_);
lean_dec(v_a_1760_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = l_Lean_Level_param___override(v_head_1763_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v_a_1761_);
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1770_ = v___x_1766_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_a_1761_);
v___x_1770_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
v_a_1760_ = v_tail_1764_;
v_a_1761_ = v___x_1770_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(lean_object* v_t_1774_, lean_object* v_k_1775_){
_start:
{
if (lean_obj_tag(v_t_1774_) == 0)
{
lean_object* v_k_1776_; lean_object* v_v_1777_; lean_object* v_l_1778_; lean_object* v_r_1779_; uint8_t v___x_1780_; 
v_k_1776_ = lean_ctor_get(v_t_1774_, 1);
v_v_1777_ = lean_ctor_get(v_t_1774_, 2);
v_l_1778_ = lean_ctor_get(v_t_1774_, 3);
v_r_1779_ = lean_ctor_get(v_t_1774_, 4);
v___x_1780_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1775_, v_k_1776_);
switch(v___x_1780_)
{
case 0:
{
v_t_1774_ = v_l_1778_;
goto _start;
}
case 1:
{
lean_object* v___x_1782_; 
lean_inc(v_v_1777_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_v_1777_);
return v___x_1782_;
}
default: 
{
v_t_1774_ = v_r_1779_;
goto _start;
}
}
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_box(0);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg___boxed(lean_object* v_t_1785_, lean_object* v_k_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_1785_, v_k_1786_);
lean_dec(v_k_1786_);
lean_dec(v_t_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1788_, lean_object* v_x2_1789_){
_start:
{
lean_object* v_fst_1790_; lean_object* v_fst_1791_; uint8_t v___x_1792_; 
v_fst_1790_ = lean_ctor_get(v_x1_1788_, 0);
v_fst_1791_ = lean_ctor_get(v_x2_1789_, 0);
v___x_1792_ = l_Lean_Name_quickLt(v_fst_1790_, v_fst_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1793_, lean_object* v_x2_1794_){
_start:
{
uint8_t v_res_1795_; lean_object* v_r_1796_; 
v_res_1795_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1793_, v_x2_1794_);
lean_dec_ref(v_x2_1794_);
lean_dec_ref(v_x1_1793_);
v_r_1796_ = lean_box(v_res_1795_);
return v_r_1796_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1797_, lean_object* v_k_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_m_1803_; lean_object* v_a_1804_; uint8_t v___x_1805_; 
v___x_1801_ = lean_nat_add(v_x_1799_, v_x_1800_);
v___x_1802_ = lean_unsigned_to_nat(1u);
v_m_1803_ = lean_nat_shiftr(v___x_1801_, v___x_1802_);
lean_dec(v___x_1801_);
v_a_1804_ = lean_array_fget_borrowed(v_as_1797_, v_m_1803_);
v___x_1805_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1804_, v_k_1798_);
if (v___x_1805_ == 0)
{
uint8_t v___x_1806_; 
lean_dec(v_x_1800_);
v___x_1806_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1798_, v_a_1804_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec(v_m_1803_);
lean_dec(v_x_1799_);
lean_inc(v_a_1804_);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1804_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_nat_dec_eq(v_m_1803_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_nat_sub(v_m_1803_, v___x_1802_);
lean_dec(v_m_1803_);
v___x_1811_ = lean_nat_dec_lt(v___x_1810_, v_x_1799_);
if (v___x_1811_ == 0)
{
v_x_1800_ = v___x_1810_;
goto _start;
}
else
{
lean_object* v___x_1813_; 
lean_dec(v___x_1810_);
lean_dec(v_x_1799_);
v___x_1813_ = lean_box(0);
return v___x_1813_;
}
}
else
{
lean_object* v___x_1814_; 
lean_dec(v_m_1803_);
lean_dec(v_x_1799_);
v___x_1814_ = lean_box(0);
return v___x_1814_;
}
}
}
else
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
lean_dec(v_x_1799_);
v___x_1815_ = lean_nat_add(v_m_1803_, v___x_1802_);
lean_dec(v_m_1803_);
v___x_1816_ = lean_nat_dec_le(v___x_1815_, v_x_1800_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
lean_dec(v___x_1815_);
lean_dec(v_x_1800_);
v___x_1817_ = lean_box(0);
return v___x_1817_;
}
else
{
v_x_1799_ = v___x_1815_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1819_, lean_object* v_k_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1819_, v_k_1820_, v_x_1821_, v_x_1822_);
lean_dec_ref(v_k_1820_);
lean_dec_ref(v_as_1819_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; lean_object* v_env_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1828_ = lean_st_ref_get(v___y_1826_);
v_env_1832_ = lean_ctor_get(v___x_1828_, 0);
lean_inc_ref(v_env_1832_);
lean_dec(v___x_1828_);
v___x_1833_ = lean_box(1);
v___x_1834_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1832_, v_tac_1825_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1835_; lean_object* v_toEnvExtension_1836_; lean_object* v_asyncMode_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1835_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_ref(v_toEnvExtension_1836_);
v_asyncMode_1837_ = lean_ctor_get(v_toEnvExtension_1836_, 2);
lean_inc(v_asyncMode_1837_);
lean_dec_ref(v_toEnvExtension_1836_);
v___x_1838_ = lean_box(0);
v___x_1839_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1833_, v___x_1835_, v_env_1832_, v_asyncMode_1837_, v___x_1838_);
lean_dec(v_asyncMode_1837_);
v___x_1840_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1839_, v_tac_1825_);
lean_dec(v_tac_1825_);
lean_dec(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
return v___x_1841_;
}
else
{
lean_object* v_val_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1870_; 
v_val_1842_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1844_ = v___x_1834_;
v_isShared_1845_ = v_isSharedCheck_1870_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_val_1842_);
lean_dec(v___x_1834_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1870_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1846_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1847_ = 0;
v___x_1848_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1833_, v___x_1846_, v_env_1832_, v_val_1842_, v___x_1847_);
lean_dec(v_val_1842_);
lean_dec_ref(v_env_1832_);
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = lean_array_get_size(v___x_1848_);
v___x_1851_ = lean_nat_dec_lt(v___x_1849_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_dec_ref(v___x_1848_);
lean_del_object(v___x_1844_);
lean_dec(v_tac_1825_);
goto v___jp_1829_;
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_sub(v___x_1850_, v___x_1852_);
v___x_1854_ = lean_nat_dec_le(v___x_1849_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_dec(v___x_1853_);
lean_dec_ref(v___x_1848_);
lean_del_object(v___x_1844_);
lean_dec(v_tac_1825_);
goto v___jp_1829_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v_tac_1825_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1848_, v___x_1856_, v___x_1849_, v___x_1853_);
lean_dec_ref(v___x_1856_);
lean_dec_ref(v___x_1848_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_del_object(v___x_1844_);
goto v___jp_1829_;
}
else
{
lean_object* v_val_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1869_; 
v_val_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_val_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v_snd_1862_; lean_object* v___x_1864_; 
v_snd_1862_ = lean_ctor_get(v_val_1858_, 1);
lean_inc(v_snd_1862_);
lean_dec(v_val_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v_snd_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_snd_1862_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1864_);
v___x_1866_ = v___x_1844_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
}
}
}
v___jp_1829_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1871_, v___y_1872_);
lean_dec(v___y_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_k_1875_, lean_object* v_v_1876_, lean_object* v_t_1877_){
_start:
{
if (lean_obj_tag(v_t_1877_) == 0)
{
lean_object* v_size_1878_; lean_object* v_k_1879_; lean_object* v_v_1880_; lean_object* v_l_1881_; lean_object* v_r_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_2163_; 
v_size_1878_ = lean_ctor_get(v_t_1877_, 0);
v_k_1879_ = lean_ctor_get(v_t_1877_, 1);
v_v_1880_ = lean_ctor_get(v_t_1877_, 2);
v_l_1881_ = lean_ctor_get(v_t_1877_, 3);
v_r_1882_ = lean_ctor_get(v_t_1877_, 4);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_t_1877_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_1884_ = v_t_1877_;
v_isShared_1885_ = v_isSharedCheck_2163_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_r_1882_);
lean_inc(v_l_1881_);
lean_inc(v_v_1880_);
lean_inc(v_k_1879_);
lean_inc(v_size_1878_);
lean_dec(v_t_1877_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_2163_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_nat_dec_lt(v_k_1875_, v_k_1879_);
if (v___x_1886_ == 0)
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_nat_dec_eq(v_k_1875_, v_k_1879_);
if (v___x_1887_ == 0)
{
lean_object* v_impl_1888_; lean_object* v___x_1889_; 
lean_dec(v_size_1878_);
v_impl_1888_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1875_, v_v_1876_, v_r_1882_);
v___x_1889_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1881_) == 0)
{
lean_object* v_size_1890_; lean_object* v_size_1891_; lean_object* v_k_1892_; lean_object* v_v_1893_; lean_object* v_l_1894_; lean_object* v_r_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_size_1890_ = lean_ctor_get(v_l_1881_, 0);
v_size_1891_ = lean_ctor_get(v_impl_1888_, 0);
lean_inc(v_size_1891_);
v_k_1892_ = lean_ctor_get(v_impl_1888_, 1);
lean_inc(v_k_1892_);
v_v_1893_ = lean_ctor_get(v_impl_1888_, 2);
lean_inc(v_v_1893_);
v_l_1894_ = lean_ctor_get(v_impl_1888_, 3);
lean_inc(v_l_1894_);
v_r_1895_ = lean_ctor_get(v_impl_1888_, 4);
lean_inc(v_r_1895_);
v___x_1896_ = lean_unsigned_to_nat(3u);
v___x_1897_ = lean_nat_mul(v___x_1896_, v_size_1890_);
v___x_1898_ = lean_nat_dec_lt(v___x_1897_, v_size_1891_);
lean_dec(v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
lean_dec(v_r_1895_);
lean_dec(v_l_1894_);
lean_dec(v_v_1893_);
lean_dec(v_k_1892_);
v___x_1899_ = lean_nat_add(v___x_1889_, v_size_1890_);
v___x_1900_ = lean_nat_add(v___x_1899_, v_size_1891_);
lean_dec(v_size_1891_);
lean_dec(v___x_1899_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v_impl_1888_);
lean_ctor_set(v___x_1884_, 0, v___x_1900_);
v___x_1902_ = v___x_1884_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_l_1881_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_impl_1888_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
else
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1967_; 
v_isSharedCheck_1967_ = !lean_is_exclusive(v_impl_1888_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; lean_object* v_unused_1972_; 
v_unused_1968_ = lean_ctor_get(v_impl_1888_, 4);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_impl_1888_, 3);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_impl_1888_, 2);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_impl_1888_, 1);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_impl_1888_, 0);
lean_dec(v_unused_1972_);
v___x_1905_ = v_impl_1888_;
v_isShared_1906_ = v_isSharedCheck_1967_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v_impl_1888_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1967_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_size_1907_; lean_object* v_k_1908_; lean_object* v_v_1909_; lean_object* v_l_1910_; lean_object* v_r_1911_; lean_object* v_size_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v_size_1907_ = lean_ctor_get(v_l_1894_, 0);
v_k_1908_ = lean_ctor_get(v_l_1894_, 1);
v_v_1909_ = lean_ctor_get(v_l_1894_, 2);
v_l_1910_ = lean_ctor_get(v_l_1894_, 3);
v_r_1911_ = lean_ctor_get(v_l_1894_, 4);
v_size_1912_ = lean_ctor_get(v_r_1895_, 0);
v___x_1913_ = lean_unsigned_to_nat(2u);
v___x_1914_ = lean_nat_mul(v___x_1913_, v_size_1912_);
v___x_1915_ = lean_nat_dec_lt(v_size_1907_, v___x_1914_);
lean_dec(v___x_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1943_; 
lean_inc(v_r_1911_);
lean_inc(v_l_1910_);
lean_inc(v_v_1909_);
lean_inc(v_k_1908_);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_l_1894_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; lean_object* v_unused_1945_; lean_object* v_unused_1946_; lean_object* v_unused_1947_; lean_object* v_unused_1948_; 
v_unused_1944_ = lean_ctor_get(v_l_1894_, 4);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_l_1894_, 3);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_l_1894_, 2);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_l_1894_, 1);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_l_1894_, 0);
lean_dec(v_unused_1948_);
v___x_1917_ = v_l_1894_;
v_isShared_1918_ = v_isSharedCheck_1943_;
goto v_resetjp_1916_;
}
else
{
lean_dec(v_l_1894_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1943_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1933_; 
v___x_1919_ = lean_nat_add(v___x_1889_, v_size_1890_);
v___x_1920_ = lean_nat_add(v___x_1919_, v_size_1891_);
lean_dec(v_size_1891_);
if (lean_obj_tag(v_l_1910_) == 0)
{
lean_object* v_size_1941_; 
v_size_1941_ = lean_ctor_get(v_l_1910_, 0);
lean_inc(v_size_1941_);
v___y_1933_ = v_size_1941_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_unsigned_to_nat(0u);
v___y_1933_ = v___x_1942_;
goto v___jp_1932_;
}
v___jp_1921_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_nat_add(v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec(v___y_1923_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 4, v_r_1895_);
lean_ctor_set(v___x_1917_, 3, v_r_1911_);
lean_ctor_set(v___x_1917_, 2, v_v_1893_);
lean_ctor_set(v___x_1917_, 1, v_k_1892_);
lean_ctor_set(v___x_1917_, 0, v___x_1925_);
v___x_1927_ = v___x_1917_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1892_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1893_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_r_1911_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_r_1895_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v___x_1927_);
lean_ctor_set(v___x_1905_, 3, v___y_1922_);
lean_ctor_set(v___x_1905_, 2, v_v_1909_);
lean_ctor_set(v___x_1905_, 1, v_k_1908_);
lean_ctor_set(v___x_1905_, 0, v___x_1920_);
v___x_1929_ = v___x_1905_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1908_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1909_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v___y_1922_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
v___jp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_nat_add(v___x_1919_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec(v___x_1919_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v_l_1910_);
lean_ctor_set(v___x_1884_, 0, v___x_1934_);
v___x_1936_ = v___x_1884_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_l_1881_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_l_1910_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_nat_add(v___x_1889_, v_size_1912_);
if (lean_obj_tag(v_r_1911_) == 0)
{
lean_object* v_size_1938_; 
v_size_1938_ = lean_ctor_get(v_r_1911_, 0);
lean_inc(v_size_1938_);
v___y_1922_ = v___x_1936_;
v___y_1923_ = v___x_1937_;
v___y_1924_ = v_size_1938_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_unsigned_to_nat(0u);
v___y_1922_ = v___x_1936_;
v___y_1923_ = v___x_1937_;
v___y_1924_ = v___x_1939_;
goto v___jp_1921_;
}
}
}
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
lean_del_object(v___x_1884_);
v___x_1949_ = lean_nat_add(v___x_1889_, v_size_1890_);
v___x_1950_ = lean_nat_add(v___x_1949_, v_size_1891_);
lean_dec(v_size_1891_);
v___x_1951_ = lean_nat_add(v___x_1949_, v_size_1907_);
lean_dec(v___x_1949_);
lean_inc_ref(v_l_1881_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v_l_1894_);
lean_ctor_set(v___x_1905_, 3, v_l_1881_);
lean_ctor_set(v___x_1905_, 2, v_v_1880_);
lean_ctor_set(v___x_1905_, 1, v_k_1879_);
lean_ctor_set(v___x_1905_, 0, v___x_1951_);
v___x_1953_ = v___x_1905_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_l_1881_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_l_1894_);
v___x_1953_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
v_isSharedCheck_1960_ = !lean_is_exclusive(v_l_1881_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; lean_object* v_unused_1962_; lean_object* v_unused_1963_; lean_object* v_unused_1964_; lean_object* v_unused_1965_; 
v_unused_1961_ = lean_ctor_get(v_l_1881_, 4);
lean_dec(v_unused_1961_);
v_unused_1962_ = lean_ctor_get(v_l_1881_, 3);
lean_dec(v_unused_1962_);
v_unused_1963_ = lean_ctor_get(v_l_1881_, 2);
lean_dec(v_unused_1963_);
v_unused_1964_ = lean_ctor_get(v_l_1881_, 1);
lean_dec(v_unused_1964_);
v_unused_1965_ = lean_ctor_get(v_l_1881_, 0);
lean_dec(v_unused_1965_);
v___x_1955_ = v_l_1881_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_dec(v_l_1881_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 4, v_r_1895_);
lean_ctor_set(v___x_1955_, 3, v___x_1953_);
lean_ctor_set(v___x_1955_, 2, v_v_1893_);
lean_ctor_set(v___x_1955_, 1, v_k_1892_);
lean_ctor_set(v___x_1955_, 0, v___x_1950_);
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_k_1892_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_v_1893_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v_r_1895_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1973_; 
v_l_1973_ = lean_ctor_get(v_impl_1888_, 3);
lean_inc(v_l_1973_);
if (lean_obj_tag(v_l_1973_) == 0)
{
lean_object* v_r_1974_; lean_object* v_k_1975_; lean_object* v_v_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1999_; 
v_r_1974_ = lean_ctor_get(v_impl_1888_, 4);
v_k_1975_ = lean_ctor_get(v_impl_1888_, 1);
v_v_1976_ = lean_ctor_get(v_impl_1888_, 2);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_impl_1888_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; lean_object* v_unused_2001_; 
v_unused_2000_ = lean_ctor_get(v_impl_1888_, 3);
lean_dec(v_unused_2000_);
v_unused_2001_ = lean_ctor_get(v_impl_1888_, 0);
lean_dec(v_unused_2001_);
v___x_1978_ = v_impl_1888_;
v_isShared_1979_ = v_isSharedCheck_1999_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_r_1974_);
lean_inc(v_v_1976_);
lean_inc(v_k_1975_);
lean_dec(v_impl_1888_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1999_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_k_1980_; lean_object* v_v_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1995_; 
v_k_1980_ = lean_ctor_get(v_l_1973_, 1);
v_v_1981_ = lean_ctor_get(v_l_1973_, 2);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_l_1973_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; lean_object* v_unused_1998_; 
v_unused_1996_ = lean_ctor_get(v_l_1973_, 4);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_l_1973_, 3);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_l_1973_, 0);
lean_dec(v_unused_1998_);
v___x_1983_ = v_l_1973_;
v_isShared_1984_ = v_isSharedCheck_1995_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_v_1981_);
lean_inc(v_k_1980_);
lean_dec(v_l_1973_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1995_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1974_, 2);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v_r_1974_);
lean_ctor_set(v___x_1983_, 3, v_r_1974_);
lean_ctor_set(v___x_1983_, 2, v_v_1880_);
lean_ctor_set(v___x_1983_, 1, v_k_1879_);
lean_ctor_set(v___x_1983_, 0, v___x_1889_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_r_1974_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_r_1974_);
v___x_1987_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
lean_inc(v_r_1974_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 3, v_r_1974_);
lean_ctor_set(v___x_1978_, 0, v___x_1889_);
v___x_1989_ = v___x_1978_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_r_1974_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_r_1974_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v___x_1989_);
lean_ctor_set(v___x_1884_, 3, v___x_1987_);
lean_ctor_set(v___x_1884_, 2, v_v_1981_);
lean_ctor_set(v___x_1884_, 1, v_k_1980_);
lean_ctor_set(v___x_1884_, 0, v___x_1985_);
v___x_1991_ = v___x_1884_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_k_1980_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_v_1981_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
}
else
{
lean_object* v_r_2002_; 
v_r_2002_ = lean_ctor_get(v_impl_1888_, 4);
lean_inc(v_r_2002_);
if (lean_obj_tag(v_r_2002_) == 0)
{
lean_object* v_k_2003_; lean_object* v_v_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2015_; 
v_k_2003_ = lean_ctor_get(v_impl_1888_, 1);
v_v_2004_ = lean_ctor_get(v_impl_1888_, 2);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_impl_1888_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; lean_object* v_unused_2017_; lean_object* v_unused_2018_; 
v_unused_2016_ = lean_ctor_get(v_impl_1888_, 4);
lean_dec(v_unused_2016_);
v_unused_2017_ = lean_ctor_get(v_impl_1888_, 3);
lean_dec(v_unused_2017_);
v_unused_2018_ = lean_ctor_get(v_impl_1888_, 0);
lean_dec(v_unused_2018_);
v___x_2006_ = v_impl_1888_;
v_isShared_2007_ = v_isSharedCheck_2015_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_v_2004_);
lean_inc(v_k_2003_);
lean_dec(v_impl_1888_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2015_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_unsigned_to_nat(3u);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 4, v_l_1973_);
lean_ctor_set(v___x_2006_, 2, v_v_1880_);
lean_ctor_set(v___x_2006_, 1, v_k_1879_);
lean_ctor_set(v___x_2006_, 0, v___x_1889_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_l_1973_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_l_1973_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v_r_2002_);
lean_ctor_set(v___x_1884_, 3, v___x_2010_);
lean_ctor_set(v___x_1884_, 2, v_v_2004_);
lean_ctor_set(v___x_1884_, 1, v_k_2003_);
lean_ctor_set(v___x_1884_, 0, v___x_2008_);
v___x_2012_ = v___x_1884_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_2003_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_2004_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_r_2002_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_unsigned_to_nat(2u);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v_impl_1888_);
lean_ctor_set(v___x_1884_, 3, v_r_2002_);
lean_ctor_set(v___x_1884_, 0, v___x_2019_);
v___x_2021_ = v___x_1884_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_r_2002_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_impl_1888_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v___x_2024_; 
lean_dec(v_v_1880_);
lean_dec(v_k_1879_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 2, v_v_1876_);
lean_ctor_set(v___x_1884_, 1, v_k_1875_);
v___x_2024_ = v___x_1884_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_size_1878_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_1875_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_1876_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_l_1881_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_r_1882_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_object* v_impl_2026_; lean_object* v___x_2027_; 
lean_dec(v_size_1878_);
v_impl_2026_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1875_, v_v_1876_, v_l_1881_);
v___x_2027_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1882_) == 0)
{
lean_object* v_size_2028_; lean_object* v_size_2029_; lean_object* v_k_2030_; lean_object* v_v_2031_; lean_object* v_l_2032_; lean_object* v_r_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_size_2028_ = lean_ctor_get(v_r_1882_, 0);
v_size_2029_ = lean_ctor_get(v_impl_2026_, 0);
lean_inc(v_size_2029_);
v_k_2030_ = lean_ctor_get(v_impl_2026_, 1);
lean_inc(v_k_2030_);
v_v_2031_ = lean_ctor_get(v_impl_2026_, 2);
lean_inc(v_v_2031_);
v_l_2032_ = lean_ctor_get(v_impl_2026_, 3);
lean_inc(v_l_2032_);
v_r_2033_ = lean_ctor_get(v_impl_2026_, 4);
lean_inc(v_r_2033_);
v___x_2034_ = lean_unsigned_to_nat(3u);
v___x_2035_ = lean_nat_mul(v___x_2034_, v_size_2028_);
v___x_2036_ = lean_nat_dec_lt(v___x_2035_, v_size_2029_);
lean_dec(v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_dec(v_r_2033_);
lean_dec(v_l_2032_);
lean_dec(v_v_2031_);
lean_dec(v_k_2030_);
v___x_2037_ = lean_nat_add(v___x_2027_, v_size_2029_);
lean_dec(v_size_2029_);
v___x_2038_ = lean_nat_add(v___x_2037_, v_size_2028_);
lean_dec(v___x_2037_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 3, v_impl_2026_);
lean_ctor_set(v___x_1884_, 0, v___x_2038_);
v___x_2040_ = v___x_1884_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_impl_2026_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_r_1882_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
else
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2107_; 
v_isSharedCheck_2107_ = !lean_is_exclusive(v_impl_2026_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; lean_object* v_unused_2109_; lean_object* v_unused_2110_; lean_object* v_unused_2111_; lean_object* v_unused_2112_; 
v_unused_2108_ = lean_ctor_get(v_impl_2026_, 4);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_impl_2026_, 3);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_impl_2026_, 2);
lean_dec(v_unused_2110_);
v_unused_2111_ = lean_ctor_get(v_impl_2026_, 1);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_impl_2026_, 0);
lean_dec(v_unused_2112_);
v___x_2043_ = v_impl_2026_;
v_isShared_2044_ = v_isSharedCheck_2107_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v_impl_2026_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2107_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_size_2045_; lean_object* v_size_2046_; lean_object* v_k_2047_; lean_object* v_v_2048_; lean_object* v_l_2049_; lean_object* v_r_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_size_2045_ = lean_ctor_get(v_l_2032_, 0);
v_size_2046_ = lean_ctor_get(v_r_2033_, 0);
v_k_2047_ = lean_ctor_get(v_r_2033_, 1);
v_v_2048_ = lean_ctor_get(v_r_2033_, 2);
v_l_2049_ = lean_ctor_get(v_r_2033_, 3);
v_r_2050_ = lean_ctor_get(v_r_2033_, 4);
v___x_2051_ = lean_unsigned_to_nat(2u);
v___x_2052_ = lean_nat_mul(v___x_2051_, v_size_2045_);
v___x_2053_ = lean_nat_dec_lt(v_size_2046_, v___x_2052_);
lean_dec(v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2082_; 
lean_inc(v_r_2050_);
lean_inc(v_l_2049_);
lean_inc(v_v_2048_);
lean_inc(v_k_2047_);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_r_2033_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; lean_object* v_unused_2084_; lean_object* v_unused_2085_; lean_object* v_unused_2086_; lean_object* v_unused_2087_; 
v_unused_2083_ = lean_ctor_get(v_r_2033_, 4);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_r_2033_, 3);
lean_dec(v_unused_2084_);
v_unused_2085_ = lean_ctor_get(v_r_2033_, 2);
lean_dec(v_unused_2085_);
v_unused_2086_ = lean_ctor_get(v_r_2033_, 1);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_r_2033_, 0);
lean_dec(v_unused_2087_);
v___x_2055_ = v_r_2033_;
v_isShared_2056_ = v_isSharedCheck_2082_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v_r_2033_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2082_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___x_2070_; lean_object* v___y_2072_; 
v___x_2057_ = lean_nat_add(v___x_2027_, v_size_2029_);
lean_dec(v_size_2029_);
v___x_2058_ = lean_nat_add(v___x_2057_, v_size_2028_);
lean_dec(v___x_2057_);
v___x_2070_ = lean_nat_add(v___x_2027_, v_size_2045_);
if (lean_obj_tag(v_l_2049_) == 0)
{
lean_object* v_size_2080_; 
v_size_2080_ = lean_ctor_get(v_l_2049_, 0);
lean_inc(v_size_2080_);
v___y_2072_ = v_size_2080_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___y_2072_ = v___x_2081_;
goto v___jp_2071_;
}
v___jp_2059_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_nat_add(v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec(v___y_2061_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 4, v_r_1882_);
lean_ctor_set(v___x_2055_, 3, v_r_2050_);
lean_ctor_set(v___x_2055_, 2, v_v_1880_);
lean_ctor_set(v___x_2055_, 1, v_k_1879_);
lean_ctor_set(v___x_2055_, 0, v___x_2063_);
v___x_2065_ = v___x_2055_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_r_2050_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_r_1882_);
v___x_2065_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 4, v___x_2065_);
lean_ctor_set(v___x_2043_, 3, v___y_2060_);
lean_ctor_set(v___x_2043_, 2, v_v_2048_);
lean_ctor_set(v___x_2043_, 1, v_k_2047_);
lean_ctor_set(v___x_2043_, 0, v___x_2058_);
v___x_2067_ = v___x_2043_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_k_2047_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_v_2048_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v___y_2060_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
v___jp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_nat_add(v___x_2070_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec(v___x_2070_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v_l_2049_);
lean_ctor_set(v___x_1884_, 3, v_l_2032_);
lean_ctor_set(v___x_1884_, 2, v_v_2031_);
lean_ctor_set(v___x_1884_, 1, v_k_2030_);
lean_ctor_set(v___x_1884_, 0, v___x_2073_);
v___x_2075_ = v___x_1884_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_2030_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_2031_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_l_2032_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_l_2049_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_nat_add(v___x_2027_, v_size_2028_);
if (lean_obj_tag(v_r_2050_) == 0)
{
lean_object* v_size_2077_; 
v_size_2077_ = lean_ctor_get(v_r_2050_, 0);
lean_inc(v_size_2077_);
v___y_2060_ = v___x_2075_;
v___y_2061_ = v___x_2076_;
v___y_2062_ = v_size_2077_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_unsigned_to_nat(0u);
v___y_2060_ = v___x_2075_;
v___y_2061_ = v___x_2076_;
v___y_2062_ = v___x_2078_;
goto v___jp_2059_;
}
}
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_del_object(v___x_1884_);
v___x_2088_ = lean_nat_add(v___x_2027_, v_size_2029_);
lean_dec(v_size_2029_);
v___x_2089_ = lean_nat_add(v___x_2088_, v_size_2028_);
lean_dec(v___x_2088_);
v___x_2090_ = lean_nat_add(v___x_2027_, v_size_2028_);
v___x_2091_ = lean_nat_add(v___x_2090_, v_size_2046_);
lean_dec(v___x_2090_);
lean_inc_ref(v_r_1882_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 4, v_r_1882_);
lean_ctor_set(v___x_2043_, 3, v_r_2033_);
lean_ctor_set(v___x_2043_, 2, v_v_1880_);
lean_ctor_set(v___x_2043_, 1, v_k_1879_);
lean_ctor_set(v___x_2043_, 0, v___x_2091_);
v___x_2093_ = v___x_2043_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_r_2033_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_r_1882_);
v___x_2093_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
v_isSharedCheck_2100_ = !lean_is_exclusive(v_r_1882_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; lean_object* v_unused_2102_; lean_object* v_unused_2103_; lean_object* v_unused_2104_; lean_object* v_unused_2105_; 
v_unused_2101_ = lean_ctor_get(v_r_1882_, 4);
lean_dec(v_unused_2101_);
v_unused_2102_ = lean_ctor_get(v_r_1882_, 3);
lean_dec(v_unused_2102_);
v_unused_2103_ = lean_ctor_get(v_r_1882_, 2);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_r_1882_, 1);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_r_1882_, 0);
lean_dec(v_unused_2105_);
v___x_2095_ = v_r_1882_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_dec(v_r_1882_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 4, v___x_2093_);
lean_ctor_set(v___x_2095_, 3, v_l_2032_);
lean_ctor_set(v___x_2095_, 2, v_v_2031_);
lean_ctor_set(v___x_2095_, 1, v_k_2030_);
lean_ctor_set(v___x_2095_, 0, v___x_2089_);
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_k_2030_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_v_2031_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_l_2032_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v___x_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2113_; 
v_l_2113_ = lean_ctor_get(v_impl_2026_, 3);
lean_inc(v_l_2113_);
if (lean_obj_tag(v_l_2113_) == 0)
{
lean_object* v_r_2114_; lean_object* v_k_2115_; lean_object* v_v_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2127_; 
v_r_2114_ = lean_ctor_get(v_impl_2026_, 4);
v_k_2115_ = lean_ctor_get(v_impl_2026_, 1);
v_v_2116_ = lean_ctor_get(v_impl_2026_, 2);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_impl_2026_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; lean_object* v_unused_2129_; 
v_unused_2128_ = lean_ctor_get(v_impl_2026_, 3);
lean_dec(v_unused_2128_);
v_unused_2129_ = lean_ctor_get(v_impl_2026_, 0);
lean_dec(v_unused_2129_);
v___x_2118_ = v_impl_2026_;
v_isShared_2119_ = v_isSharedCheck_2127_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_r_2114_);
lean_inc(v_v_2116_);
lean_inc(v_k_2115_);
lean_dec(v_impl_2026_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2127_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2114_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 3, v_r_2114_);
lean_ctor_set(v___x_2118_, 2, v_v_1880_);
lean_ctor_set(v___x_2118_, 1, v_k_1879_);
lean_ctor_set(v___x_2118_, 0, v___x_2027_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_r_2114_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v_r_2114_);
v___x_2122_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v___x_2122_);
lean_ctor_set(v___x_1884_, 3, v_l_2113_);
lean_ctor_set(v___x_1884_, 2, v_v_2116_);
lean_ctor_set(v___x_1884_, 1, v_k_2115_);
lean_ctor_set(v___x_1884_, 0, v___x_2120_);
v___x_2124_ = v___x_1884_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_l_2113_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_r_2130_; 
v_r_2130_ = lean_ctor_get(v_impl_2026_, 4);
lean_inc(v_r_2130_);
if (lean_obj_tag(v_r_2130_) == 0)
{
lean_object* v_k_2131_; lean_object* v_v_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2155_; 
v_k_2131_ = lean_ctor_get(v_impl_2026_, 1);
v_v_2132_ = lean_ctor_get(v_impl_2026_, 2);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_impl_2026_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2156_ = lean_ctor_get(v_impl_2026_, 4);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_impl_2026_, 3);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_impl_2026_, 0);
lean_dec(v_unused_2158_);
v___x_2134_ = v_impl_2026_;
v_isShared_2135_ = v_isSharedCheck_2155_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_v_2132_);
lean_inc(v_k_2131_);
lean_dec(v_impl_2026_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2155_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v_k_2136_; lean_object* v_v_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2151_; 
v_k_2136_ = lean_ctor_get(v_r_2130_, 1);
v_v_2137_ = lean_ctor_get(v_r_2130_, 2);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_r_2130_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; lean_object* v_unused_2153_; lean_object* v_unused_2154_; 
v_unused_2152_ = lean_ctor_get(v_r_2130_, 4);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_r_2130_, 3);
lean_dec(v_unused_2153_);
v_unused_2154_ = lean_ctor_get(v_r_2130_, 0);
lean_dec(v_unused_2154_);
v___x_2139_ = v_r_2130_;
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_v_2137_);
lean_inc(v_k_2136_);
lean_dec(v_r_2130_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2151_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_unsigned_to_nat(3u);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 4, v_l_2113_);
lean_ctor_set(v___x_2139_, 3, v_l_2113_);
lean_ctor_set(v___x_2139_, 2, v_v_2132_);
lean_ctor_set(v___x_2139_, 1, v_k_2131_);
lean_ctor_set(v___x_2139_, 0, v___x_2027_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_k_2131_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_v_2132_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v_l_2113_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_l_2113_);
v___x_2143_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2145_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 4, v_l_2113_);
lean_ctor_set(v___x_2134_, 2, v_v_1880_);
lean_ctor_set(v___x_2134_, 1, v_k_1879_);
lean_ctor_set(v___x_2134_, 0, v___x_2027_);
v___x_2145_ = v___x_2134_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_l_2113_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_l_2113_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v___x_2145_);
lean_ctor_set(v___x_1884_, 3, v___x_2143_);
lean_ctor_set(v___x_1884_, 2, v_v_2137_);
lean_ctor_set(v___x_1884_, 1, v_k_2136_);
lean_ctor_set(v___x_1884_, 0, v___x_2141_);
v___x_2147_ = v___x_1884_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_2136_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_2137_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_unsigned_to_nat(2u);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 4, v_r_2130_);
lean_ctor_set(v___x_1884_, 3, v_impl_2026_);
lean_ctor_set(v___x_1884_, 0, v___x_2159_);
v___x_2161_ = v___x_1884_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_k_1879_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_v_1880_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_impl_2026_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_r_2130_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v_k_1875_);
lean_ctor_set(v___x_2165_, 2, v_v_1876_);
lean_ctor_set(v___x_2165_, 3, v_t_1877_);
lean_ctor_set(v___x_2165_, 4, v_t_1877_);
return v___x_2165_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_as_x27_2166_, lean_object* v_b_2167_){
_start:
{
if (lean_obj_tag(v_as_x27_2166_) == 0)
{
return v_b_2167_;
}
else
{
lean_object* v_head_2168_; lean_object* v_tail_2169_; lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v_r_2172_; 
v_head_2168_ = lean_ctor_get(v_as_x27_2166_, 0);
lean_inc(v_head_2168_);
v_tail_2169_ = lean_ctor_get(v_as_x27_2166_, 1);
lean_inc(v_tail_2169_);
lean_dec_ref(v_as_x27_2166_);
v_fst_2170_ = lean_ctor_get(v_head_2168_, 0);
lean_inc(v_fst_2170_);
v_snd_2171_ = lean_ctor_get(v_head_2168_, 1);
lean_inc(v_snd_2171_);
lean_dec(v_head_2168_);
v_r_2172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_fst_2170_, v_snd_2171_, v_b_2167_);
v_as_x27_2166_ = v_tail_2169_;
v_b_2167_ = v_r_2172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_2174_, lean_object* v_n_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2212_; lean_object* v_val_2213_; lean_object* v___x_2215_; lean_object* v___y_2217_; lean_object* v_env_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2215_ = lean_st_ref_get(v___y_2177_);
v_env_2232_ = lean_ctor_get(v___x_2215_, 0);
lean_inc_ref(v_env_2232_);
lean_dec(v___x_2215_);
v___x_2233_ = l_Lean_Environment_constants(v_env_2232_);
v___x_2234_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v___x_2233_, v_n_2175_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_box(0);
v___y_2217_ = v___x_2235_;
goto v___jp_2216_;
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_val_2236_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_val_2236_);
lean_dec_ref(v___x_2234_);
v___x_2237_ = l_Lean_ConstantInfo_levelParams(v_val_2236_);
lean_dec(v_val_2236_);
v___x_2238_ = lean_box(0);
v___x_2239_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(v___x_2237_, v___x_2238_);
v___y_2217_ = v___x_2239_;
goto v___jp_2216_;
}
v___jp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_r_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v___y_2181_);
v___x_2185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2182_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___x_2182_);
v___x_2187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_2188_ = lean_box(2);
v___x_2189_ = 1;
lean_inc(v_n_2175_);
v___x_2190_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_2175_, v___x_2189_);
v___x_2191_ = lean_string_utf8_byte_size(v___x_2190_);
v___x_2192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2183_);
lean_ctor_set(v___x_2192_, 2, v___x_2191_);
v___x_2193_ = lean_box(0);
lean_inc(v_n_2175_);
v___x_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2194_, 0, v_n_2175_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v___x_2193_);
lean_inc(v_n_2175_);
v___x_2196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2188_);
lean_ctor_set(v___x_2196_, 1, v___x_2192_);
lean_ctor_set(v___x_2196_, 2, v_n_2175_);
lean_ctor_set(v___x_2196_, 3, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2187_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_LocalContext_empty;
v___x_2199_ = lean_box(0);
v___x_2200_ = l_Lean_Expr_const___override(v_n_2175_, v___y_2180_);
v___x_2201_ = 0;
v___x_2202_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2202_, 0, v___x_2197_);
lean_ctor_set(v___x_2202_, 1, v___x_2198_);
lean_ctor_set(v___x_2202_, 2, v___x_2199_);
lean_ctor_set(v___x_2202_, 3, v___x_2200_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*4, v___x_2201_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*4 + 1, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2183_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2193_);
v_r_2206_ = lean_box(1);
v___x_2207_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_2205_, v_r_2206_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2186_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
v___jp_2211_:
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_val_2213_);
v___y_2180_ = v___y_2212_;
v___y_2181_ = v___x_2214_;
goto v___jp_2179_;
}
v___jp_2216_:
{
lean_object* v___x_2218_; lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2231_; 
lean_inc(v_n_2175_);
v___x_2218_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_2175_, v___y_2177_);
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2231_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2231_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
if (lean_obj_tag(v_a_2219_) == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_firsts_2174_, v_n_2175_);
if (lean_obj_tag(v___x_2223_) == 0)
{
uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = 1;
lean_inc(v_n_2175_);
v___x_2225_ = l_Lean_Name_toString(v_n_2175_, v___x_2224_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 3);
lean_ctor_set(v___x_2221_, 0, v___x_2225_);
v___x_2227_ = v___x_2221_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
v___y_2180_ = v___y_2217_;
v___y_2181_ = v___x_2227_;
goto v___jp_2179_;
}
}
else
{
lean_object* v_val_2229_; 
lean_del_object(v___x_2221_);
v_val_2229_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_val_2229_);
lean_dec_ref(v___x_2223_);
v___y_2212_ = v___y_2217_;
v_val_2213_ = v_val_2229_;
goto v___jp_2211_;
}
}
else
{
lean_object* v_val_2230_; 
lean_del_object(v___x_2221_);
v_val_2230_ = lean_ctor_get(v_a_2219_, 0);
lean_inc(v_val_2230_);
lean_dec_ref(v_a_2219_);
v___y_2212_ = v___y_2217_;
v_val_2213_ = v_val_2230_;
goto v___jp_2211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_2240_, lean_object* v_n_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_2240_, v_n_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v_firsts_2240_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
if (lean_obj_tag(v_x_2247_) == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = l_List_reverse___redArg(v_x_2248_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
else
{
lean_object* v_head_2254_; lean_object* v_tail_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2273_; 
v_head_2254_ = lean_ctor_get(v_x_2247_, 0);
v_tail_2255_ = lean_ctor_get(v_x_2247_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_x_2247_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2257_ = v_x_2247_;
v_isShared_2258_ = v_isSharedCheck_2273_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_tail_2255_);
lean_inc(v_head_2254_);
lean_dec(v_x_2247_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2273_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_2246_, v_head_2254_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 1, v_x_2248_);
lean_ctor_set(v___x_2257_, 0, v_a_2260_);
v___x_2262_ = v___x_2257_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2260_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_x_2248_);
v___x_2262_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
v_x_2247_ = v_tail_2255_;
v_x_2248_ = v___x_2262_;
goto _start;
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_del_object(v___x_2257_);
lean_dec(v_tail_2255_);
lean_dec(v_x_2248_);
v_a_2265_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2259_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2259_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2274_, v_x_2275_, v_x_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v_a_2274_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_2281_, lean_object* v___x_2282_, lean_object* v___x_2283_, lean_object* v_a_2284_, lean_object* v_b_2285_){
_start:
{
lean_object* v_it_2287_; lean_object* v_startInclusive_2288_; lean_object* v_endExclusive_2289_; 
if (lean_obj_tag(v_a_2284_) == 0)
{
lean_object* v_currPos_2294_; lean_object* v_searcher_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2321_; 
v_currPos_2294_ = lean_ctor_get(v_a_2284_, 0);
v_searcher_2295_ = lean_ctor_get(v_a_2284_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_a_2284_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2297_ = v_a_2284_;
v_isShared_2298_ = v_isSharedCheck_2321_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_searcher_2295_);
lean_inc(v_currPos_2294_);
lean_dec(v_a_2284_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2321_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_startInclusive_2299_; lean_object* v_endExclusive_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_startInclusive_2299_ = lean_ctor_get(v___x_2282_, 1);
v_endExclusive_2300_ = lean_ctor_get(v___x_2282_, 2);
v___x_2301_ = lean_nat_sub(v_endExclusive_2300_, v_startInclusive_2299_);
v___x_2302_ = lean_nat_dec_eq(v_searcher_2295_, v___x_2301_);
lean_dec(v___x_2301_);
if (v___x_2302_ == 0)
{
uint32_t v___x_2303_; uint32_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2303_ = 10;
v___x_2304_ = lean_string_utf8_get_fast(v_val_2281_, v_searcher_2295_);
v___x_2305_ = lean_uint32_dec_eq(v___x_2304_, v___x_2303_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = lean_string_utf8_next_fast(v_val_2281_, v_searcher_2295_);
lean_dec(v_searcher_2295_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2306_);
v___x_2308_ = v___x_2297_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_currPos_2294_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
v_a_2284_ = v___x_2308_;
goto _start;
}
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v_slice_2314_; lean_object* v_nextIt_2316_; 
v___x_2311_ = lean_string_utf8_next_fast(v_val_2281_, v_searcher_2295_);
v___x_2312_ = lean_nat_sub(v___x_2311_, v_searcher_2295_);
v___x_2313_ = lean_nat_add(v_searcher_2295_, v___x_2312_);
lean_dec(v___x_2312_);
v_slice_2314_ = l_String_Slice_subslice_x21(v___x_2282_, v_currPos_2294_, v_searcher_2295_);
lean_inc(v___x_2313_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2313_);
lean_ctor_set(v___x_2297_, 0, v___x_2313_);
v_nextIt_2316_ = v___x_2297_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2313_);
v_nextIt_2316_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v_startInclusive_2317_; lean_object* v_endExclusive_2318_; 
v_startInclusive_2317_ = lean_ctor_get(v_slice_2314_, 0);
lean_inc(v_startInclusive_2317_);
v_endExclusive_2318_ = lean_ctor_get(v_slice_2314_, 1);
lean_inc(v_endExclusive_2318_);
lean_dec_ref(v_slice_2314_);
v_it_2287_ = v_nextIt_2316_;
v_startInclusive_2288_ = v_startInclusive_2317_;
v_endExclusive_2289_ = v_endExclusive_2318_;
goto v___jp_2286_;
}
}
}
else
{
lean_object* v___x_2320_; 
lean_del_object(v___x_2297_);
lean_dec(v_searcher_2295_);
v___x_2320_ = lean_box(1);
lean_inc(v___x_2283_);
v_it_2287_ = v___x_2320_;
v_startInclusive_2288_ = v_currPos_2294_;
v_endExclusive_2289_ = v___x_2283_;
goto v___jp_2286_;
}
}
}
else
{
lean_dec(v___x_2283_);
return v_b_2285_;
}
v___jp_2286_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_string_utf8_extract(v_val_2281_, v_startInclusive_2288_, v_endExclusive_2289_);
lean_dec(v_endExclusive_2289_);
lean_dec(v_startInclusive_2288_);
v___x_2291_ = l_Lean_stringToMessageData(v___x_2290_);
v___x_2292_ = lean_array_push(v_b_2285_, v___x_2291_);
v_a_2284_ = v_it_2287_;
v_b_2285_ = v___x_2292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2322_, lean_object* v___x_2323_, lean_object* v___x_2324_, lean_object* v_a_2325_, lean_object* v_b_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2322_, v___x_2323_, v___x_2324_, v_a_2325_, v_b_2326_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v_val_2322_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(lean_object* v_init_2328_, lean_object* v_x_2329_){
_start:
{
if (lean_obj_tag(v_x_2329_) == 0)
{
lean_object* v_k_2330_; lean_object* v_l_2331_; lean_object* v_r_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_k_2330_ = lean_ctor_get(v_x_2329_, 1);
lean_inc(v_k_2330_);
v_l_2331_ = lean_ctor_get(v_x_2329_, 3);
lean_inc(v_l_2331_);
v_r_2332_ = lean_ctor_get(v_x_2329_, 4);
lean_inc(v_r_2332_);
lean_dec_ref(v_x_2329_);
v___x_2333_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_2328_, v_l_2331_);
v___x_2334_ = lean_array_push(v___x_2333_, v_k_2330_);
v_init_2328_ = v___x_2334_;
v_x_2329_ = v_r_2332_;
goto _start;
}
else
{
return v_init_2328_;
}
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2343_ = l_Lean_stringToMessageData(v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
return v___x_2346_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2351_ = l_Lean_MessageData_ofFormat(v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_x_2354_, lean_object* v_x_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
if (lean_obj_tag(v_x_2354_) == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = l_List_reverse___redArg(v_x_2355_);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
else
{
lean_object* v_head_2361_; lean_object* v_tail_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2459_; 
v_head_2361_ = lean_ctor_get(v_x_2354_, 0);
v_tail_2362_ = lean_ctor_get(v_x_2354_, 1);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_x_2354_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2364_ = v_x_2354_;
v_isShared_2365_ = v_isSharedCheck_2459_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_tail_2362_);
lean_inc(v_head_2361_);
lean_dec(v_x_2354_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2459_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v_snd_2379_; lean_object* v_fst_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2458_; 
v_snd_2379_ = lean_ctor_get(v_head_2361_, 1);
v_fst_2380_ = lean_ctor_get(v_head_2361_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_head_2361_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2382_ = v_head_2361_;
v_isShared_2383_ = v_isSharedCheck_2458_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_snd_2379_);
lean_inc(v_fst_2380_);
lean_dec(v_head_2361_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2458_;
goto v_resetjp_2381_;
}
v___jp_2366_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___y_2369_);
lean_ctor_set(v___x_2371_, 1, v___y_2370_);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v___y_2368_);
v___x_2373_ = l_Lean_MessageData_nestD(v___x_2372_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___y_2367_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v_x_2355_);
lean_ctor_set(v___x_2364_, 0, v___x_2374_);
v___x_2376_ = v___x_2364_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_x_2355_);
v___x_2376_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
v_x_2354_ = v_tail_2362_;
v_x_2355_ = v___x_2376_;
goto _start;
}
}
v_resetjp_2381_:
{
lean_object* v_fst_2384_; lean_object* v_snd_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2457_; 
v_fst_2384_ = lean_ctor_get(v_snd_2379_, 0);
v_snd_2385_ = lean_ctor_get(v_snd_2379_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_snd_2379_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2387_ = v_snd_2379_;
v_isShared_2388_ = v_isSharedCheck_2457_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_snd_2385_);
lean_inc(v_fst_2384_);
lean_dec(v_snd_2379_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2457_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v_a_2412_; lean_object* v___y_2428_; lean_object* v___x_2437_; 
v___x_2437_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2353_, v_fst_2380_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_MessageData_nil;
v_a_2412_ = v___x_2438_;
goto v___jp_2411_;
}
else
{
lean_object* v_val_2439_; 
v_val_2439_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_val_2439_);
lean_dec_ref(v___x_2437_);
if (lean_obj_tag(v_val_2439_) == 0)
{
lean_object* v_size_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v_size_2440_ = lean_ctor_get(v_val_2439_, 0);
v___x_2441_ = lean_mk_empty_array_with_capacity(v_size_2440_);
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v___x_2441_, v_val_2439_);
v___x_2447_ = lean_array_get_size(v___x_2442_);
v___x_2448_ = lean_unsigned_to_nat(0u);
v___x_2449_ = lean_nat_dec_eq(v___x_2447_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___y_2453_; uint8_t v___x_2455_; 
v___x_2450_ = lean_unsigned_to_nat(1u);
v___x_2451_ = lean_nat_sub(v___x_2447_, v___x_2450_);
v___x_2455_ = lean_nat_dec_le(v___x_2448_, v___x_2451_);
if (v___x_2455_ == 0)
{
lean_inc(v___x_2451_);
v___y_2453_ = v___x_2451_;
goto v___jp_2452_;
}
else
{
v___y_2453_ = v___x_2448_;
goto v___jp_2452_;
}
v___jp_2452_:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_nat_dec_le(v___y_2453_, v___x_2451_);
if (v___x_2454_ == 0)
{
lean_dec(v___x_2451_);
lean_inc(v___y_2453_);
v___y_2444_ = v___y_2453_;
v___y_2445_ = v___y_2453_;
goto v___jp_2443_;
}
else
{
v___y_2444_ = v___y_2453_;
v___y_2445_ = v___x_2451_;
goto v___jp_2443_;
}
}
}
else
{
v___y_2428_ = v___x_2442_;
goto v___jp_2427_;
}
v___jp_2443_:
{
lean_object* v___x_2446_; 
v___x_2446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2442_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
v___y_2428_ = v___x_2446_;
goto v___jp_2427_;
}
}
else
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_MessageData_nil;
v_a_2412_ = v___x_2456_;
goto v___jp_2411_;
}
}
v___jp_2389_:
{
lean_object* v___x_2395_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set_tag(v___x_2387_, 7);
lean_ctor_set(v___x_2387_, 1, v___y_2393_);
lean_ctor_set(v___x_2387_, 0, v___y_2392_);
v___x_2395_ = v___x_2387_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___y_2392_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___y_2393_);
v___x_2395_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
if (lean_obj_tag(v_snd_2385_) == 0)
{
lean_object* v___x_2396_; 
lean_del_object(v___x_2382_);
v___x_2396_ = l_Lean_MessageData_nil;
v___y_2367_ = v___y_2390_;
v___y_2368_ = v___y_2391_;
v___y_2369_ = v___x_2395_;
v___y_2370_ = v___x_2396_;
goto v___jp_2366_;
}
else
{
lean_object* v_val_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v_val_2397_ = lean_ctor_get(v_snd_2385_, 0);
lean_inc(v_val_2397_);
lean_dec_ref(v_snd_2385_);
v___x_2398_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2399_ = lean_unsigned_to_nat(0u);
v___x_2400_ = lean_string_utf8_byte_size(v_val_2397_);
lean_inc(v_val_2397_);
v___x_2401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2401_, 0, v_val_2397_);
lean_ctor_set(v___x_2401_, 1, v___x_2399_);
lean_ctor_set(v___x_2401_, 2, v___x_2400_);
v___x_2402_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2401_);
v___x_2403_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2404_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2397_, v___x_2401_, v___x_2400_, v___x_2402_, v___x_2403_);
lean_dec_ref(v___x_2401_);
lean_dec(v_val_2397_);
v___x_2405_ = lean_array_to_list(v___x_2404_);
v___x_2406_ = l_Lean_MessageData_joinSep(v___x_2405_, v___x_2398_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 7);
lean_ctor_set(v___x_2382_, 1, v___x_2406_);
lean_ctor_set(v___x_2382_, 0, v___x_2398_);
v___x_2408_ = v___x_2382_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
v___y_2367_ = v___y_2390_;
v___y_2368_ = v___y_2391_;
v___y_2369_ = v___x_2395_;
v___y_2370_ = v___x_2408_;
goto v___jp_2366_;
}
}
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2413_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2414_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2380_);
v___x_2415_ = l_Lean_MessageData_ofName(v_fst_2380_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v___x_2414_);
v___x_2418_ = 1;
v___x_2419_ = l_Lean_Name_toString(v_fst_2380_, v___x_2418_);
v___x_2420_ = lean_string_dec_eq(v___x_2419_, v_fst_2384_);
lean_dec_ref(v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2421_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2422_ = l_Lean_stringToMessageData(v_fst_2384_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___y_2390_ = v___x_2413_;
v___y_2391_ = v_a_2412_;
v___y_2392_ = v___x_2417_;
v___y_2393_ = v___x_2425_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2426_; 
lean_dec(v_fst_2384_);
v___x_2426_ = l_Lean_MessageData_nil;
v___y_2390_ = v___x_2413_;
v___y_2391_ = v_a_2412_;
v___y_2392_ = v___x_2417_;
v___y_2393_ = v___x_2426_;
goto v___jp_2389_;
}
}
v___jp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = lean_array_to_list(v___y_2428_);
v___x_2430_ = lean_box(0);
v___x_2431_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2352_, v___x_2429_, v___x_2430_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref(v___x_2431_);
v___x_2433_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2434_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2435_ = l_Lean_MessageData_joinSep(v_a_2432_, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2433_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v_a_2412_ = v___x_2436_;
goto v___jp_2411_;
}
else
{
lean_del_object(v___x_2387_);
lean_dec(v_snd_2385_);
lean_dec(v_fst_2384_);
lean_del_object(v___x_2382_);
lean_dec(v_fst_2380_);
lean_del_object(v___x_2364_);
lean_dec(v_tail_2362_);
lean_dec(v_x_2355_);
return v___x_2431_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2460_, v_a_2461_, v_x_2462_, v_x_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v_a_2461_);
lean_dec(v_a_2460_);
return v_res_2467_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(uint8_t v___y_2469_, uint8_t v_suppressElabErrors_2470_, lean_object* v_x_2471_){
_start:
{
if (lean_obj_tag(v_x_2471_) == 1)
{
lean_object* v_pre_2472_; 
v_pre_2472_ = lean_ctor_get(v_x_2471_, 0);
if (lean_obj_tag(v_pre_2472_) == 0)
{
lean_object* v_str_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v_str_2473_ = lean_ctor_get(v_x_2471_, 1);
v___x_2474_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0));
v___x_2475_ = lean_string_dec_eq(v_str_2473_, v___x_2474_);
if (v___x_2475_ == 0)
{
return v___y_2469_;
}
else
{
return v_suppressElabErrors_2470_;
}
}
else
{
return v___y_2469_;
}
}
else
{
return v___y_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed(lean_object* v___y_2476_, lean_object* v_suppressElabErrors_2477_, lean_object* v_x_2478_){
_start:
{
uint8_t v___y_19652__boxed_2479_; uint8_t v_suppressElabErrors_boxed_2480_; uint8_t v_res_2481_; lean_object* v_r_2482_; 
v___y_19652__boxed_2479_ = lean_unbox(v___y_2476_);
v_suppressElabErrors_boxed_2480_ = lean_unbox(v_suppressElabErrors_2477_);
v_res_2481_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(v___y_19652__boxed_2479_, v_suppressElabErrors_boxed_2480_, v_x_2478_);
lean_dec(v_x_2478_);
v_r_2482_ = lean_box(v_res_2481_);
return v_r_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(lean_object* v_ref_2483_, lean_object* v_msgData_2484_, uint8_t v_severity_2485_, uint8_t v_isSilent_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; uint8_t v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; uint8_t v___y_2554_; uint8_t v___y_2555_; lean_object* v___y_2556_; uint8_t v___y_2557_; lean_object* v___y_2558_; uint8_t v___y_2582_; uint8_t v___y_2583_; lean_object* v___y_2584_; uint8_t v___y_2585_; lean_object* v___y_2586_; uint8_t v___y_2590_; uint8_t v___y_2591_; uint8_t v___y_2592_; uint8_t v___x_2607_; uint8_t v___y_2609_; uint8_t v___y_2610_; uint8_t v___y_2611_; uint8_t v___y_2613_; uint8_t v___x_2625_; 
v___x_2607_ = 2;
v___x_2625_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2485_, v___x_2607_);
if (v___x_2625_ == 0)
{
v___y_2613_ = v___x_2625_;
goto v___jp_2612_;
}
else
{
uint8_t v___x_2626_; 
lean_inc_ref(v_msgData_2484_);
v___x_2626_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2484_);
v___y_2613_ = v___x_2626_;
goto v___jp_2612_;
}
v___jp_2490_:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Elab_Command_getScope___redArg(v___y_2498_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = l_Lean_Elab_Command_getScope___redArg(v___y_2498_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2536_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2536_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2536_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v_currNamespace_2507_; lean_object* v_openDecls_2508_; lean_object* v_env_2509_; lean_object* v_messages_2510_; lean_object* v_scopes_2511_; lean_object* v_usedQuotCtxts_2512_; lean_object* v_nextMacroScope_2513_; lean_object* v_maxRecDepth_2514_; lean_object* v_ngen_2515_; lean_object* v_auxDeclNGen_2516_; lean_object* v_infoState_2517_; lean_object* v_traceState_2518_; lean_object* v_snapshotTasks_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2535_; 
v___x_2506_ = lean_st_ref_take(v___y_2498_);
v_currNamespace_2507_ = lean_ctor_get(v_a_2500_, 2);
lean_inc(v_currNamespace_2507_);
lean_dec(v_a_2500_);
v_openDecls_2508_ = lean_ctor_get(v_a_2502_, 3);
lean_inc(v_openDecls_2508_);
lean_dec(v_a_2502_);
v_env_2509_ = lean_ctor_get(v___x_2506_, 0);
v_messages_2510_ = lean_ctor_get(v___x_2506_, 1);
v_scopes_2511_ = lean_ctor_get(v___x_2506_, 2);
v_usedQuotCtxts_2512_ = lean_ctor_get(v___x_2506_, 3);
v_nextMacroScope_2513_ = lean_ctor_get(v___x_2506_, 4);
v_maxRecDepth_2514_ = lean_ctor_get(v___x_2506_, 5);
v_ngen_2515_ = lean_ctor_get(v___x_2506_, 6);
v_auxDeclNGen_2516_ = lean_ctor_get(v___x_2506_, 7);
v_infoState_2517_ = lean_ctor_get(v___x_2506_, 8);
v_traceState_2518_ = lean_ctor_get(v___x_2506_, 9);
v_snapshotTasks_2519_ = lean_ctor_get(v___x_2506_, 10);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2521_ = v___x_2506_;
v_isShared_2522_ = v_isSharedCheck_2535_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_snapshotTasks_2519_);
lean_inc(v_traceState_2518_);
lean_inc(v_infoState_2517_);
lean_inc(v_auxDeclNGen_2516_);
lean_inc(v_ngen_2515_);
lean_inc(v_maxRecDepth_2514_);
lean_inc(v_nextMacroScope_2513_);
lean_inc(v_usedQuotCtxts_2512_);
lean_inc(v_scopes_2511_);
lean_inc(v_messages_2510_);
lean_inc(v_env_2509_);
lean_dec(v___x_2506_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2535_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_currNamespace_2507_);
lean_ctor_set(v___x_2523_, 1, v_openDecls_2508_);
v___x_2524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___y_2494_);
v___x_2525_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2525_, 0, v___y_2493_);
lean_ctor_set(v___x_2525_, 1, v___y_2492_);
lean_ctor_set(v___x_2525_, 2, v___y_2497_);
lean_ctor_set(v___x_2525_, 3, v___y_2495_);
lean_ctor_set(v___x_2525_, 4, v___x_2524_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*5, v___y_2496_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*5 + 1, v___y_2491_);
lean_ctor_set_uint8(v___x_2525_, sizeof(void*)*5 + 2, v_isSilent_2486_);
v___x_2526_ = l_Lean_MessageLog_add(v___x_2525_, v_messages_2510_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v___x_2526_);
v___x_2528_ = v___x_2521_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_env_2509_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_scopes_2511_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_usedQuotCtxts_2512_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v_nextMacroScope_2513_);
lean_ctor_set(v_reuseFailAlloc_2534_, 5, v_maxRecDepth_2514_);
lean_ctor_set(v_reuseFailAlloc_2534_, 6, v_ngen_2515_);
lean_ctor_set(v_reuseFailAlloc_2534_, 7, v_auxDeclNGen_2516_);
lean_ctor_set(v_reuseFailAlloc_2534_, 8, v_infoState_2517_);
lean_ctor_set(v_reuseFailAlloc_2534_, 9, v_traceState_2518_);
lean_ctor_set(v_reuseFailAlloc_2534_, 10, v_snapshotTasks_2519_);
v___x_2528_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = lean_st_ref_set(v___y_2498_, v___x_2528_);
v___x_2530_ = lean_box(0);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2530_);
v___x_2532_ = v___x_2504_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_a_2500_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2492_);
v_a_2537_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2501_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2501_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2492_);
v_a_2545_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2499_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2499_);
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
v___jp_2553_:
{
lean_object* v_fileName_2559_; lean_object* v_fileMap_2560_; uint8_t v_suppressElabErrors_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2580_; 
v_fileName_2559_ = lean_ctor_get(v___y_2487_, 0);
lean_inc_ref(v_fileName_2559_);
v_fileMap_2560_ = lean_ctor_get(v___y_2487_, 1);
lean_inc_ref(v_fileMap_2560_);
v_suppressElabErrors_2561_ = lean_ctor_get_uint8(v___y_2487_, sizeof(void*)*10);
lean_dec_ref(v___y_2487_);
v___x_2562_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2484_);
v___x_2563_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2562_, v___y_2488_);
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2580_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2580_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_inc_ref(v_fileMap_2560_);
v___x_2568_ = l_Lean_FileMap_toPosition(v_fileMap_2560_, v___y_2556_);
lean_dec(v___y_2556_);
v___x_2569_ = l_Lean_FileMap_toPosition(v_fileMap_2560_, v___y_2558_);
lean_dec(v___y_2558_);
v___x_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
v___x_2571_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2561_ == 0)
{
lean_del_object(v___x_2566_);
v___y_2491_ = v___y_2555_;
v___y_2492_ = v___x_2568_;
v___y_2493_ = v_fileName_2559_;
v___y_2494_ = v_a_2564_;
v___y_2495_ = v___x_2571_;
v___y_2496_ = v___y_2557_;
v___y_2497_ = v___x_2570_;
v___y_2498_ = v___y_2488_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___f_2574_; uint8_t v___x_2575_; 
v___x_2572_ = lean_box(v___y_2554_);
v___x_2573_ = lean_box(v_suppressElabErrors_2561_);
v___f_2574_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2574_, 0, v___x_2572_);
lean_closure_set(v___f_2574_, 1, v___x_2573_);
lean_inc(v_a_2564_);
v___x_2575_ = l_Lean_MessageData_hasTag(v___f_2574_, v_a_2564_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_dec_ref(v___x_2570_);
lean_dec_ref(v___x_2568_);
lean_dec(v_a_2564_);
lean_dec_ref(v_fileName_2559_);
v___x_2576_ = lean_box(0);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2576_);
v___x_2578_ = v___x_2566_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
else
{
lean_del_object(v___x_2566_);
v___y_2491_ = v___y_2555_;
v___y_2492_ = v___x_2568_;
v___y_2493_ = v_fileName_2559_;
v___y_2494_ = v_a_2564_;
v___y_2495_ = v___x_2571_;
v___y_2496_ = v___y_2557_;
v___y_2497_ = v___x_2570_;
v___y_2498_ = v___y_2488_;
goto v___jp_2490_;
}
}
}
}
v___jp_2581_:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Syntax_getTailPos_x3f(v___y_2584_, v___y_2585_);
lean_dec(v___y_2584_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_inc(v___y_2586_);
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___y_2586_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v___y_2586_;
goto v___jp_2553_;
}
else
{
lean_object* v_val_2588_; 
v_val_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_val_2588_);
lean_dec_ref(v___x_2587_);
v___y_2554_ = v___y_2582_;
v___y_2555_ = v___y_2583_;
v___y_2556_ = v___y_2586_;
v___y_2557_ = v___y_2585_;
v___y_2558_ = v_val_2588_;
goto v___jp_2553_;
}
}
v___jp_2589_:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Elab_Command_getRef___redArg(v___y_2487_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v_ref_2595_; lean_object* v___x_2596_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v_ref_2595_ = l_Lean_replaceRef(v_ref_2483_, v_a_2594_);
lean_dec(v_a_2594_);
v___x_2596_ = l_Lean_Syntax_getPos_x3f(v_ref_2595_, v___y_2591_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_unsigned_to_nat(0u);
v___y_2582_ = v___y_2590_;
v___y_2583_ = v___y_2592_;
v___y_2584_ = v_ref_2595_;
v___y_2585_ = v___y_2591_;
v___y_2586_ = v___x_2597_;
goto v___jp_2581_;
}
else
{
lean_object* v_val_2598_; 
v_val_2598_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_val_2598_);
lean_dec_ref(v___x_2596_);
v___y_2582_ = v___y_2590_;
v___y_2583_ = v___y_2592_;
v___y_2584_ = v_ref_2595_;
v___y_2585_ = v___y_2591_;
v___y_2586_ = v_val_2598_;
goto v___jp_2581_;
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v___y_2487_);
lean_dec_ref(v_msgData_2484_);
v_a_2599_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2593_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2593_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
v___jp_2608_:
{
if (v___y_2611_ == 0)
{
v___y_2590_ = v___y_2609_;
v___y_2591_ = v___y_2610_;
v___y_2592_ = v_severity_2485_;
goto v___jp_2589_;
}
else
{
v___y_2590_ = v___y_2609_;
v___y_2591_ = v___y_2610_;
v___y_2592_ = v___x_2607_;
goto v___jp_2589_;
}
}
v___jp_2612_:
{
if (v___y_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v_scopes_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_opts_2618_; uint8_t v___x_2619_; uint8_t v___x_2620_; 
v___x_2614_ = lean_st_ref_get(v___y_2488_);
v_scopes_2615_ = lean_ctor_get(v___x_2614_, 2);
lean_inc(v_scopes_2615_);
lean_dec(v___x_2614_);
v___x_2616_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2617_ = l_List_head_x21___redArg(v___x_2616_, v_scopes_2615_);
lean_dec(v_scopes_2615_);
v_opts_2618_ = lean_ctor_get(v___x_2617_, 1);
lean_inc_ref(v_opts_2618_);
lean_dec(v___x_2617_);
v___x_2619_ = 1;
v___x_2620_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2485_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_dec_ref(v_opts_2618_);
v___y_2609_ = v___y_2613_;
v___y_2610_ = v___y_2613_;
v___y_2611_ = v___x_2620_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = l_Lean_warningAsError;
v___x_2622_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2618_, v___x_2621_);
lean_dec_ref(v_opts_2618_);
v___y_2609_ = v___y_2613_;
v___y_2610_ = v___y_2613_;
v___y_2611_ = v___x_2622_;
goto v___jp_2608_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec_ref(v___y_2487_);
lean_dec_ref(v_msgData_2484_);
v___x_2623_ = lean_box(0);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___boxed(lean_object* v_ref_2627_, lean_object* v_msgData_2628_, lean_object* v_severity_2629_, lean_object* v_isSilent_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v_severity_boxed_2634_; uint8_t v_isSilent_boxed_2635_; lean_object* v_res_2636_; 
v_severity_boxed_2634_ = lean_unbox(v_severity_2629_);
v_isSilent_boxed_2635_ = lean_unbox(v_isSilent_2630_);
v_res_2636_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(v_ref_2627_, v_msgData_2628_, v_severity_boxed_2634_, v_isSilent_boxed_2635_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec(v_ref_2627_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(lean_object* v_msgData_2637_, uint8_t v_severity_2638_, uint8_t v_isSilent_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_Elab_Command_getRef___redArg(v___y_2640_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
lean_inc_ref(v___y_2640_);
v___x_2645_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(v_a_2644_, v_msgData_2637_, v_severity_2638_, v_isSilent_2639_, v___y_2640_, v___y_2641_);
lean_dec(v_a_2644_);
return v___x_2645_;
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v_msgData_2637_);
v_a_2646_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2643_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2643_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27___boxed(lean_object* v_msgData_2654_, lean_object* v_severity_2655_, lean_object* v_isSilent_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v_severity_boxed_2660_; uint8_t v_isSilent_boxed_2661_; lean_object* v_res_2662_; 
v_severity_boxed_2660_ = lean_unbox(v_severity_2655_);
v_isSilent_boxed_2661_ = lean_unbox(v_isSilent_2656_);
v_res_2662_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(v_msgData_2654_, v_severity_boxed_2660_, v_isSilent_boxed_2661_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v___x_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = 0;
v___x_2668_ = 0;
v___x_2669_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(v_msgData_2663_, v___x_2667_, v___x_2668_, v___y_2664_, v___y_2665_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(lean_object* v_init_2675_, lean_object* v_x_2676_){
_start:
{
if (lean_obj_tag(v_x_2676_) == 0)
{
lean_object* v_k_2677_; lean_object* v_v_2678_; lean_object* v_l_2679_; lean_object* v_r_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_k_2677_ = lean_ctor_get(v_x_2676_, 1);
v_v_2678_ = lean_ctor_get(v_x_2676_, 2);
v_l_2679_ = lean_ctor_get(v_x_2676_, 3);
v_r_2680_ = lean_ctor_get(v_x_2676_, 4);
v___x_2681_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_2675_, v_l_2679_);
lean_inc(v_v_2678_);
lean_inc(v_k_2677_);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_k_2677_);
lean_ctor_set(v___x_2682_, 1, v_v_2678_);
v___x_2683_ = lean_array_push(v___x_2681_, v___x_2682_);
v_init_2675_ = v___x_2683_;
v_x_2676_ = v_r_2680_;
goto _start;
}
else
{
return v_init_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26___boxed(lean_object* v_init_2685_, lean_object* v_x_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_2685_, v_x_2686_);
lean_dec(v_x_2686_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(lean_object* v_as_2688_, size_t v_sz_2689_, size_t v_i_2690_, lean_object* v_b_2691_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_usize_dec_lt(v_i_2690_, v_sz_2689_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_b_2691_);
return v___x_2694_;
}
else
{
lean_object* v_a_2695_; lean_object* v_fst_2696_; lean_object* v_snd_2697_; lean_object* v_found_2698_; size_t v___x_2699_; size_t v___x_2700_; 
v_a_2695_ = lean_array_uget_borrowed(v_as_2688_, v_i_2690_);
v_fst_2696_ = lean_ctor_get(v_a_2695_, 0);
v_snd_2697_ = lean_ctor_get(v_a_2695_, 1);
lean_inc(v_snd_2697_);
lean_inc(v_fst_2696_);
v_found_2698_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2696_, v_snd_2697_, v_b_2691_);
v___x_2699_ = ((size_t)1ULL);
v___x_2700_ = lean_usize_add(v_i_2690_, v___x_2699_);
v_i_2690_ = v___x_2700_;
v_b_2691_ = v_found_2698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg___boxed(lean_object* v_as_2702_, lean_object* v_sz_2703_, lean_object* v_i_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_){
_start:
{
size_t v_sz_boxed_2707_; size_t v_i_boxed_2708_; lean_object* v_res_2709_; 
v_sz_boxed_2707_ = lean_unbox_usize(v_sz_2703_);
lean_dec(v_sz_2703_);
v_i_boxed_2708_ = lean_unbox_usize(v_i_2704_);
lean_dec(v_i_2704_);
v_res_2709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_as_2702_, v_sz_boxed_2707_, v_i_boxed_2708_, v_b_2705_);
lean_dec_ref(v_as_2702_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_as_2710_, size_t v_sz_2711_, size_t v_i_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
uint8_t v___x_2717_; 
v___x_2717_ = lean_usize_dec_lt(v_i_2712_, v_sz_2711_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_b_2713_);
return v___x_2718_;
}
else
{
lean_object* v_a_2719_; size_t v_sz_2720_; size_t v___x_2721_; lean_object* v___x_2722_; 
v_a_2719_ = lean_array_uget_borrowed(v_as_2710_, v_i_2712_);
v_sz_2720_ = lean_array_size(v_a_2719_);
v___x_2721_ = ((size_t)0ULL);
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_a_2719_, v_sz_2720_, v___x_2721_, v_b_2713_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; size_t v___x_2724_; size_t v___x_2725_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref(v___x_2722_);
v___x_2724_ = ((size_t)1ULL);
v___x_2725_ = lean_usize_add(v_i_2712_, v___x_2724_);
v_i_2712_ = v___x_2725_;
v_b_2713_ = v_a_2723_;
goto _start;
}
else
{
return v___x_2722_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_as_2727_, lean_object* v_sz_2728_, lean_object* v_i_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
size_t v_sz_boxed_2734_; size_t v_i_boxed_2735_; lean_object* v_res_2736_; 
v_sz_boxed_2734_ = lean_unbox_usize(v_sz_2728_);
lean_dec(v_sz_2728_);
v_i_boxed_2735_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_as_2727_, v_sz_boxed_2734_, v_i_boxed_2735_, v_b_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v_as_2727_);
return v_res_2736_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(uint8_t v___x_2737_, lean_object* v_x1_2738_, lean_object* v_x2_2739_){
_start:
{
lean_object* v_fst_2740_; lean_object* v_fst_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v_fst_2740_ = lean_ctor_get(v_x1_2738_, 0);
lean_inc(v_fst_2740_);
lean_dec_ref(v_x1_2738_);
v_fst_2741_ = lean_ctor_get(v_x2_2739_, 0);
lean_inc(v_fst_2741_);
lean_dec_ref(v_x2_2739_);
v___x_2742_ = l_Lean_Name_toString(v_fst_2740_, v___x_2737_);
v___x_2743_ = l_Lean_Name_toString(v_fst_2741_, v___x_2737_);
v___x_2744_ = lean_string_dec_lt(v___x_2742_, v___x_2743_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v___x_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed(lean_object* v___x_2745_, lean_object* v_x1_2746_, lean_object* v_x2_2747_){
_start:
{
uint8_t v___x_20027__boxed_2748_; uint8_t v_res_2749_; lean_object* v_r_2750_; 
v___x_20027__boxed_2748_ = lean_unbox(v___x_2745_);
v_res_2749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(v___x_20027__boxed_2748_, v_x1_2746_, v_x2_2747_);
v_r_2750_ = lean_box(v_res_2749_);
return v_r_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_as_2751_, lean_object* v_lo_2752_, lean_object* v_hi_2753_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_nat_dec_lt(v_lo_2752_, v_hi_2753_);
if (v___x_2754_ == 0)
{
lean_dec(v_lo_2752_);
return v_as_2751_;
}
else
{
lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; lean_object* v_fst_2758_; lean_object* v_snd_2759_; uint8_t v___x_2760_; 
v___x_2755_ = lean_box(v___x_2754_);
v___f_2756_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2756_, 0, v___x_2755_);
lean_inc(v_lo_2752_);
v___x_2757_ = l_Array_qpartition___redArg(v_as_2751_, v___f_2756_, v_lo_2752_, v_hi_2753_);
v_fst_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_fst_2758_);
v_snd_2759_ = lean_ctor_get(v___x_2757_, 1);
lean_inc(v_snd_2759_);
lean_dec_ref(v___x_2757_);
v___x_2760_ = lean_nat_dec_le(v_hi_2753_, v_fst_2758_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_snd_2759_, v_lo_2752_, v_fst_2758_);
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_nat_add(v_fst_2758_, v___x_2762_);
lean_dec(v_fst_2758_);
v_as_2751_ = v___x_2761_;
v_lo_2752_ = v___x_2763_;
goto _start;
}
else
{
lean_dec(v_fst_2758_);
lean_dec(v_lo_2752_);
return v_snd_2759_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_as_2765_, lean_object* v_lo_2766_, lean_object* v_hi_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_as_2765_, v_lo_2766_, v_hi_2767_);
lean_dec(v_hi_2767_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object* v_init_2769_, lean_object* v_x_2770_){
_start:
{
if (lean_obj_tag(v_x_2770_) == 0)
{
lean_object* v_k_2772_; lean_object* v_v_2773_; lean_object* v_l_2774_; lean_object* v_r_2775_; lean_object* v___x_2776_; lean_object* v_a_2777_; lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_k_2772_ = lean_ctor_get(v_x_2770_, 1);
lean_inc(v_k_2772_);
v_v_2773_ = lean_ctor_get(v_x_2770_, 2);
lean_inc(v_v_2773_);
v_l_2774_ = lean_ctor_get(v_x_2770_, 3);
lean_inc(v_l_2774_);
v_r_2775_ = lean_ctor_get(v_x_2770_, 4);
lean_inc(v_r_2775_);
lean_dec_ref(v_x_2770_);
v___x_2776_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_2769_, v_l_2774_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref(v___x_2776_);
v_a_2778_ = lean_ctor_get(v_a_2777_, 0);
lean_inc(v_a_2778_);
lean_dec(v_a_2777_);
v___x_2779_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2772_, v_v_2773_, v_a_2778_);
v_init_2769_ = v___x_2779_;
v_x_2770_ = v_r_2775_;
goto _start;
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2781_, 0, v_init_2769_);
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object* v_init_2783_, lean_object* v_x_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_2783_, v_x_2784_);
return v_res_2786_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_box(1);
v___x_2788_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___y_2795_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___x_2810_; lean_object* v_env_2811_; lean_object* v___x_2812_; lean_object* v_toEnvExtension_2813_; lean_object* v_asyncMode_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v_a_2820_; lean_object* v_a_2822_; lean_object* v_a_2845_; 
v___x_2810_ = lean_st_ref_get(v___y_2792_);
v_env_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc_ref(v_env_2811_);
lean_dec(v___x_2810_);
v___x_2812_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc_ref(v_toEnvExtension_2813_);
v_asyncMode_2814_ = lean_ctor_get(v_toEnvExtension_2813_, 2);
lean_inc(v_asyncMode_2814_);
v___x_2815_ = lean_box(1);
v___x_2816_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2817_ = lean_box(0);
lean_inc_ref(v_env_2811_);
v___x_2818_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2815_, v___x_2812_, v_env_2811_, v_asyncMode_2814_, v___x_2817_);
v___x_2819_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v___x_2815_, v___x_2818_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2819_);
v_a_2845_ = lean_ctor_get(v_a_2820_, 0);
lean_inc(v_a_2845_);
lean_dec(v_a_2820_);
v_a_2822_ = v_a_2845_;
goto v___jp_2821_;
v___jp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_array_to_list(v___y_2795_);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
return v___x_2797_;
}
v___jp_2798_:
{
lean_object* v___x_2803_; 
lean_dec(v___y_2799_);
v___x_2803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
v___y_2795_ = v___x_2803_;
goto v___jp_2794_;
}
v___jp_2804_:
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_nat_dec_le(v___y_2808_, v___y_2807_);
if (v___x_2809_ == 0)
{
lean_dec(v___y_2807_);
lean_inc(v___y_2808_);
v___y_2799_ = v___y_2805_;
v___y_2800_ = v___y_2806_;
v___y_2801_ = v___y_2808_;
v___y_2802_ = v___y_2808_;
goto v___jp_2798_;
}
else
{
v___y_2799_ = v___y_2805_;
v___y_2800_ = v___y_2806_;
v___y_2801_ = v___y_2808_;
v___y_2802_ = v___y_2807_;
goto v___jp_2798_;
}
}
v___jp_2821_:
{
lean_object* v___x_2823_; lean_object* v_importedEntries_2824_; size_t v_sz_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2823_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2816_, v_toEnvExtension_2813_, v_env_2811_, v_asyncMode_2814_, v___x_2817_);
lean_dec(v_asyncMode_2814_);
lean_dec_ref(v_toEnvExtension_2813_);
v_importedEntries_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc_ref(v_importedEntries_2824_);
lean_dec(v___x_2823_);
v_sz_2825_ = lean_array_size(v_importedEntries_2824_);
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_importedEntries_2824_, v_sz_2825_, v___x_2826_, v_a_2822_, v___y_2791_, v___y_2792_);
lean_dec_ref(v_importedEntries_2824_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v_arr_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = lean_unsigned_to_nat(0u);
v___x_2830_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2831_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v___x_2830_, v_a_2828_);
lean_dec(v_a_2828_);
v___x_2832_ = lean_array_get_size(v_arr_2831_);
v___x_2833_ = lean_nat_dec_eq(v___x_2832_, v___x_2829_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; 
v___x_2834_ = lean_unsigned_to_nat(1u);
v___x_2835_ = lean_nat_sub(v___x_2832_, v___x_2834_);
v___x_2836_ = lean_nat_dec_le(v___x_2829_, v___x_2835_);
if (v___x_2836_ == 0)
{
lean_inc(v___x_2835_);
v___y_2805_ = v___x_2832_;
v___y_2806_ = v_arr_2831_;
v___y_2807_ = v___x_2835_;
v___y_2808_ = v___x_2835_;
goto v___jp_2804_;
}
else
{
v___y_2805_ = v___x_2832_;
v___y_2806_ = v_arr_2831_;
v___y_2807_ = v___x_2835_;
v___y_2808_ = v___x_2829_;
goto v___jp_2804_;
}
}
else
{
v___y_2795_ = v_arr_2831_;
goto v___jp_2794_;
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
v_a_2837_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2827_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2827_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2850_, lean_object* v_k_2851_, lean_object* v_fallback_2852_){
_start:
{
if (lean_obj_tag(v_t_2850_) == 0)
{
lean_object* v_k_2853_; lean_object* v_v_2854_; lean_object* v_l_2855_; lean_object* v_r_2856_; uint8_t v___x_2857_; 
v_k_2853_ = lean_ctor_get(v_t_2850_, 1);
v_v_2854_ = lean_ctor_get(v_t_2850_, 2);
v_l_2855_ = lean_ctor_get(v_t_2850_, 3);
v_r_2856_ = lean_ctor_get(v_t_2850_, 4);
v___x_2857_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2851_, v_k_2853_);
switch(v___x_2857_)
{
case 0:
{
v_t_2850_ = v_l_2855_;
goto _start;
}
case 1:
{
lean_inc(v_v_2854_);
return v_v_2854_;
}
default: 
{
v_t_2850_ = v_r_2856_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2852_);
return v_fallback_2852_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2860_, lean_object* v_k_2861_, lean_object* v_fallback_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2860_, v_k_2861_, v_fallback_2862_);
lean_dec(v_fallback_2862_);
lean_dec(v_k_2861_);
lean_dec(v_t_2860_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2864_, size_t v_sz_2865_, size_t v_i_2866_, lean_object* v_b_2867_){
_start:
{
uint8_t v___x_2869_; 
v___x_2869_ = lean_usize_dec_lt(v_i_2866_, v_sz_2865_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; 
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v_b_2867_);
return v___x_2870_;
}
else
{
lean_object* v_a_2871_; lean_object* v_fst_2872_; lean_object* v_snd_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; size_t v___x_2878_; size_t v___x_2879_; 
v_a_2871_ = lean_array_uget_borrowed(v_as_2864_, v_i_2866_);
v_fst_2872_ = lean_ctor_get(v_a_2871_, 0);
v_snd_2873_ = lean_ctor_get(v_a_2871_, 1);
v___x_2874_ = l_Lean_NameSet_empty;
v___x_2875_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2867_, v_snd_2873_, v___x_2874_);
lean_inc(v_fst_2872_);
v___x_2876_ = l_Lean_NameSet_insert(v___x_2875_, v_fst_2872_);
lean_inc(v_snd_2873_);
v___x_2877_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2873_, v___x_2876_, v_b_2867_);
v___x_2878_ = ((size_t)1ULL);
v___x_2879_ = lean_usize_add(v_i_2866_, v___x_2878_);
v_i_2866_ = v___x_2879_;
v_b_2867_ = v___x_2877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2881_, lean_object* v_sz_2882_, lean_object* v_i_2883_, lean_object* v_b_2884_, lean_object* v___y_2885_){
_start:
{
size_t v_sz_boxed_2886_; size_t v_i_boxed_2887_; lean_object* v_res_2888_; 
v_sz_boxed_2886_ = lean_unbox_usize(v_sz_2882_);
lean_dec(v_sz_2882_);
v_i_boxed_2887_ = lean_unbox_usize(v_i_2883_);
lean_dec(v_i_2883_);
v_res_2888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2881_, v_sz_boxed_2886_, v_i_boxed_2887_, v_b_2884_);
lean_dec_ref(v_as_2881_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2889_, size_t v_sz_2890_, size_t v_i_2891_, lean_object* v_b_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v___x_2896_; 
v___x_2896_ = lean_usize_dec_lt(v_i_2891_, v_sz_2890_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_b_2892_);
return v___x_2897_;
}
else
{
lean_object* v_a_2898_; size_t v_sz_2899_; size_t v___x_2900_; lean_object* v___x_2901_; 
v_a_2898_ = lean_array_uget_borrowed(v_as_2889_, v_i_2891_);
v_sz_2899_ = lean_array_size(v_a_2898_);
v___x_2900_ = ((size_t)0ULL);
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2898_, v_sz_2899_, v___x_2900_, v_b_2892_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; size_t v___x_2903_; size_t v___x_2904_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
v___x_2903_ = ((size_t)1ULL);
v___x_2904_ = lean_usize_add(v_i_2891_, v___x_2903_);
v_i_2891_ = v___x_2904_;
v_b_2892_ = v_a_2902_;
goto _start;
}
else
{
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2906_, lean_object* v_sz_2907_, lean_object* v_i_2908_, lean_object* v_b_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
size_t v_sz_boxed_2913_; size_t v_i_boxed_2914_; lean_object* v_res_2915_; 
v_sz_boxed_2913_ = lean_unbox_usize(v_sz_2907_);
lean_dec(v_sz_2907_);
v_i_boxed_2914_ = lean_unbox_usize(v_i_2908_);
lean_dec(v_i_2908_);
v_res_2915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2906_, v_sz_boxed_2913_, v_i_boxed_2914_, v_b_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v_as_2906_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2916_, size_t v_i_2917_, size_t v_stop_2918_, lean_object* v_b_2919_){
_start:
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_usize_dec_eq(v_i_2917_, v_stop_2918_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; lean_object* v_fst_2922_; lean_object* v_snd_2923_; lean_object* v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; 
v___x_2921_ = lean_array_uget_borrowed(v_as_2916_, v_i_2917_);
v_fst_2922_ = lean_ctor_get(v___x_2921_, 0);
v_snd_2923_ = lean_ctor_get(v___x_2921_, 1);
lean_inc(v_snd_2923_);
lean_inc(v_fst_2922_);
v___x_2924_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2922_, v_snd_2923_, v_b_2919_);
v___x_2925_ = ((size_t)1ULL);
v___x_2926_ = lean_usize_add(v_i_2917_, v___x_2925_);
v_i_2917_ = v___x_2926_;
v_b_2919_ = v___x_2924_;
goto _start;
}
else
{
return v_b_2919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2928_, lean_object* v_i_2929_, lean_object* v_stop_2930_, lean_object* v_b_2931_){
_start:
{
size_t v_i_boxed_2932_; size_t v_stop_boxed_2933_; lean_object* v_res_2934_; 
v_i_boxed_2932_ = lean_unbox_usize(v_i_2929_);
lean_dec(v_i_2929_);
v_stop_boxed_2933_ = lean_unbox_usize(v_stop_2930_);
lean_dec(v_stop_2930_);
v_res_2934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2928_, v_i_boxed_2932_, v_stop_boxed_2933_, v_b_2931_);
lean_dec_ref(v_as_2928_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2935_, size_t v_i_2936_, size_t v_stop_2937_, lean_object* v_b_2938_){
_start:
{
lean_object* v___y_2940_; uint8_t v___x_2944_; 
v___x_2944_ = lean_usize_dec_eq(v_i_2936_, v_stop_2937_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v___x_2945_ = lean_array_uget_borrowed(v_as_2935_, v_i_2936_);
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = lean_array_get_size(v___x_2945_);
v___x_2948_ = lean_nat_dec_lt(v___x_2946_, v___x_2947_);
if (v___x_2948_ == 0)
{
v___y_2940_ = v_b_2938_;
goto v___jp_2939_;
}
else
{
uint8_t v___x_2949_; 
v___x_2949_ = lean_nat_dec_le(v___x_2947_, v___x_2947_);
if (v___x_2949_ == 0)
{
if (v___x_2948_ == 0)
{
v___y_2940_ = v_b_2938_;
goto v___jp_2939_;
}
else
{
size_t v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = ((size_t)0ULL);
v___x_2951_ = lean_usize_of_nat(v___x_2947_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2945_, v___x_2950_, v___x_2951_, v_b_2938_);
v___y_2940_ = v___x_2952_;
goto v___jp_2939_;
}
}
else
{
size_t v___x_2953_; size_t v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = ((size_t)0ULL);
v___x_2954_ = lean_usize_of_nat(v___x_2947_);
v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2945_, v___x_2953_, v___x_2954_, v_b_2938_);
v___y_2940_ = v___x_2955_;
goto v___jp_2939_;
}
}
}
else
{
return v_b_2938_;
}
v___jp_2939_:
{
size_t v___x_2941_; size_t v___x_2942_; 
v___x_2941_ = ((size_t)1ULL);
v___x_2942_ = lean_usize_add(v_i_2936_, v___x_2941_);
v_i_2936_ = v___x_2942_;
v_b_2938_ = v___y_2940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2956_, lean_object* v_i_2957_, lean_object* v_stop_2958_, lean_object* v_b_2959_){
_start:
{
size_t v_i_boxed_2960_; size_t v_stop_boxed_2961_; lean_object* v_res_2962_; 
v_i_boxed_2960_ = lean_unbox_usize(v_i_2957_);
lean_dec(v_i_2957_);
v_stop_boxed_2961_ = lean_unbox_usize(v_stop_2958_);
lean_dec(v_stop_2958_);
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2956_, v_i_boxed_2960_, v_stop_boxed_2961_, v_b_2959_);
lean_dec_ref(v_as_2956_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; lean_object* v_env_2966_; lean_object* v___x_2967_; lean_object* v_ext_2968_; lean_object* v_toEnvExtension_2969_; lean_object* v_asyncMode_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_categories_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2965_ = lean_st_ref_get(v___y_2963_);
v_env_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc_ref(v_env_2966_);
lean_dec(v___x_2965_);
v___x_2967_ = l_Lean_Parser_parserExtension;
v_ext_2968_ = lean_ctor_get(v___x_2967_, 1);
lean_inc_ref(v_ext_2968_);
v_toEnvExtension_2969_ = lean_ctor_get(v_ext_2968_, 0);
lean_inc_ref(v_toEnvExtension_2969_);
lean_dec_ref(v_ext_2968_);
v_asyncMode_2970_ = lean_ctor_get(v_toEnvExtension_2969_, 2);
lean_inc(v_asyncMode_2970_);
lean_dec_ref(v_toEnvExtension_2969_);
v___x_2971_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2966_);
v___x_2972_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2971_, v___x_2967_, v_env_2966_, v_asyncMode_2970_);
lean_dec(v_asyncMode_2970_);
v_categories_2973_ = lean_ctor_get(v___x_2972_, 2);
lean_inc_ref(v_categories_2973_);
lean_dec(v___x_2972_);
v___x_2974_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2975_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2973_, v___x_2974_);
if (lean_obj_tag(v___x_2975_) == 1)
{
lean_object* v_val_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3014_; 
v_val_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_3014_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_val_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3014_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___y_2981_; lean_object* v___x_2990_; lean_object* v_toEnvExtension_2991_; lean_object* v_exportEntriesFn_2992_; lean_object* v_asyncMode_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_importedEntries_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_2990_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc_ref(v_toEnvExtension_2991_);
v_exportEntriesFn_2992_ = lean_ctor_get(v___x_2990_, 4);
lean_inc_ref(v_exportEntriesFn_2992_);
v_asyncMode_2993_ = lean_ctor_get(v_toEnvExtension_2991_, 2);
lean_inc(v_asyncMode_2993_);
v___x_2994_ = lean_box(1);
v___x_2995_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2996_ = lean_box(0);
lean_inc_ref(v_env_2966_);
v___x_2997_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2995_, v_toEnvExtension_2991_, v_env_2966_, v_asyncMode_2993_, v___x_2996_);
lean_dec_ref(v_toEnvExtension_2991_);
v_importedEntries_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc_ref(v_importedEntries_2998_);
lean_dec(v___x_2997_);
lean_inc_ref(v_env_2966_);
v___x_2999_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2994_, v___x_2990_, v_env_2966_, v_asyncMode_2993_, v___x_2996_);
lean_dec(v_asyncMode_2993_);
v___x_3000_ = 0;
v___x_3001_ = lean_box(v___x_3000_);
v___x_3002_ = lean_apply_3(v_exportEntriesFn_2992_, v_env_2966_, v___x_2999_, v___x_3001_);
v___x_3003_ = lean_array_push(v_importedEntries_2998_, v___x_3002_);
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = lean_array_get_size(v___x_3003_);
v___x_3006_ = lean_nat_dec_lt(v___x_3004_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_dec_ref(v___x_3003_);
v___y_2981_ = v___x_2994_;
goto v___jp_2980_;
}
else
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_nat_dec_le(v___x_3005_, v___x_3005_);
if (v___x_3007_ == 0)
{
if (v___x_3006_ == 0)
{
lean_dec_ref(v___x_3003_);
v___y_2981_ = v___x_2994_;
goto v___jp_2980_;
}
else
{
size_t v___x_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = lean_usize_of_nat(v___x_3005_);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3003_, v___x_3008_, v___x_3009_, v___x_2994_);
lean_dec_ref(v___x_3003_);
v___y_2981_ = v___x_3010_;
goto v___jp_2980_;
}
}
else
{
size_t v___x_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = ((size_t)0ULL);
v___x_3012_ = lean_usize_of_nat(v___x_3005_);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3003_, v___x_3011_, v___x_3012_, v___x_2994_);
lean_dec_ref(v___x_3003_);
v___y_2981_ = v___x_3013_;
goto v___jp_2980_;
}
}
v___jp_2980_:
{
lean_object* v_tables_2982_; lean_object* v_leadingTable_2983_; lean_object* v_trailingTable_2984_; lean_object* v_firstTokens_2985_; lean_object* v_firstTokens_2986_; lean_object* v___x_2988_; 
v_tables_2982_ = lean_ctor_get(v_val_2976_, 2);
v_leadingTable_2983_ = lean_ctor_get(v_tables_2982_, 0);
v_trailingTable_2984_ = lean_ctor_get(v_tables_2982_, 2);
lean_inc(v_trailingTable_2984_);
lean_inc(v_leadingTable_2983_);
lean_inc(v_val_2976_);
v_firstTokens_2985_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2976_, v_leadingTable_2983_, v___y_2981_);
v_firstTokens_2986_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2976_, v_trailingTable_2984_, v_firstTokens_2985_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set_tag(v___x_2978_, 0);
lean_ctor_set(v___x_2978_, 0, v_firstTokens_2986_);
v___x_2988_ = v___x_2978_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_firstTokens_2986_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
lean_dec(v___x_2975_);
lean_dec_ref(v_env_2966_);
v___x_3015_ = lean_box(1);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3017_);
lean_dec(v___y_3017_);
return v_res_3019_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_box(1);
v___x_3021_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3020_);
return v___x_3021_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_3024_ = l_Lean_stringToMessageData(v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v_env_3031_; lean_object* v_env_3032_; lean_object* v_env_3033_; lean_object* v___x_3034_; lean_object* v_toEnvExtension_3035_; lean_object* v_exportEntriesFn_3036_; lean_object* v_asyncMode_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_importedEntries_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3095_; 
v___x_3028_ = lean_st_ref_get(v_a_3026_);
v___x_3029_ = lean_st_ref_get(v_a_3026_);
v___x_3030_ = lean_st_ref_get(v_a_3026_);
v_env_3031_ = lean_ctor_get(v___x_3028_, 0);
lean_inc_ref(v_env_3031_);
lean_dec(v___x_3028_);
v_env_3032_ = lean_ctor_get(v___x_3029_, 0);
lean_inc_ref(v_env_3032_);
lean_dec(v___x_3029_);
v_env_3033_ = lean_ctor_get(v___x_3030_, 0);
lean_inc_ref(v_env_3033_);
lean_dec(v___x_3030_);
v___x_3034_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc_ref(v_toEnvExtension_3035_);
v_exportEntriesFn_3036_ = lean_ctor_get(v___x_3034_, 4);
lean_inc_ref(v_exportEntriesFn_3036_);
v_asyncMode_3037_ = lean_ctor_get(v_toEnvExtension_3035_, 2);
lean_inc(v_asyncMode_3037_);
v___x_3038_ = lean_box(1);
v___x_3039_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3040_ = lean_box(0);
v___x_3041_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3039_, v_toEnvExtension_3035_, v_env_3031_, v_asyncMode_3037_, v___x_3040_);
lean_dec_ref(v_toEnvExtension_3035_);
v_importedEntries_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; 
v_unused_3096_ = lean_ctor_get(v___x_3041_, 1);
lean_dec(v_unused_3096_);
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3095_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_importedEntries_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3095_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; size_t v_sz_3051_; size_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3046_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3038_, v___x_3034_, v_env_3033_, v_asyncMode_3037_, v___x_3040_);
lean_dec(v_asyncMode_3037_);
v___x_3047_ = 0;
v___x_3048_ = lean_box(v___x_3047_);
v___x_3049_ = lean_apply_3(v_exportEntriesFn_3036_, v_env_3032_, v___x_3046_, v___x_3048_);
v___x_3050_ = lean_array_push(v_importedEntries_3042_, v___x_3049_);
v_sz_3051_ = lean_array_size(v___x_3050_);
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_3050_, v_sz_3051_, v___x_3052_, v___x_3038_, v_a_3025_, v_a_3026_);
lean_dec_ref(v___x_3050_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v_a_3056_; lean_object* v___x_3057_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
v___x_3055_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_3026_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_3025_, v_a_3026_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref(v___x_3057_);
v___x_3059_ = lean_box(0);
v___x_3060_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3056_, v_a_3054_, v_a_3058_, v___x_3059_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3054_);
lean_dec(v_a_3056_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3066_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref(v___x_3060_);
v___x_3062_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_3063_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_3064_ = l_Lean_MessageData_joinSep(v_a_3061_, v___x_3063_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set_tag(v___x_3044_, 7);
lean_ctor_set(v___x_3044_, 1, v___x_3064_);
lean_ctor_set(v___x_3044_, 0, v___x_3063_);
v___x_3066_ = v___x_3044_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = l_Lean_MessageData_nestD(v___x_3066_);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3062_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_3068_, v_a_3025_, v_a_3026_);
return v___x_3069_;
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_del_object(v___x_3044_);
v_a_3071_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3060_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3060_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_3056_);
lean_dec(v_a_3054_);
lean_del_object(v___x_3044_);
v_a_3079_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3057_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3057_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_del_object(v___x_3044_);
v_a_3087_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3053_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3053_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3097_, v_a_3098_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3102_, v_a_3103_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_3106_, v_a_3107_, v_a_3108_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
lean_dec(v___stx_3106_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_3111_, lean_object* v_t_3112_, lean_object* v_k_3113_, lean_object* v_fallback_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3112_, v_k_3113_, v_fallback_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_3116_, lean_object* v_t_3117_, lean_object* v_k_3118_, lean_object* v_fallback_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_3116_, v_t_3117_, v_k_3118_, v_fallback_3119_);
lean_dec(v_fallback_3119_);
lean_dec(v_k_3118_);
lean_dec(v_t_3117_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_3121_, size_t v_sz_3122_, size_t v_i_3123_, lean_object* v_b_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3121_, v_sz_3122_, v_i_3123_, v_b_3124_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_3129_, lean_object* v_sz_3130_, lean_object* v_i_3131_, lean_object* v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
size_t v_sz_boxed_3136_; size_t v_i_boxed_3137_; lean_object* v_res_3138_; 
v_sz_boxed_3136_ = lean_unbox_usize(v_sz_3130_);
lean_dec(v_sz_3130_);
v_i_boxed_3137_ = lean_unbox_usize(v_i_3131_);
lean_dec(v_i_3131_);
v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_3129_, v_sz_boxed_3136_, v_i_boxed_3137_, v_b_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v_as_3129_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_3147_, lean_object* v___x_3148_, lean_object* v___x_3149_, lean_object* v_inst_3150_, lean_object* v_R_3151_, lean_object* v_a_3152_, lean_object* v_b_3153_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3147_, v___x_3148_, v___x_3149_, v_a_3152_, v_b_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_3155_, lean_object* v___x_3156_, lean_object* v___x_3157_, lean_object* v_inst_3158_, lean_object* v_R_3159_, lean_object* v_a_3160_, lean_object* v_b_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_3155_, v___x_3156_, v___x_3157_, v_inst_3158_, v_R_3159_, v_a_3160_, v_b_3161_);
lean_dec_ref(v___x_3156_);
lean_dec_ref(v_val_3155_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_3163_, lean_object* v_t_3164_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_3163_, v_t_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_3166_, lean_object* v_as_3167_, lean_object* v_lo_3168_, lean_object* v_hi_3169_, lean_object* v_w_3170_, lean_object* v_hlo_3171_, lean_object* v_hhi_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_as_3167_, v_lo_3168_, v_hi_3169_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_3174_, lean_object* v_as_3175_, lean_object* v_lo_3176_, lean_object* v_hi_3177_, lean_object* v_w_3178_, lean_object* v_hlo_3179_, lean_object* v_hhi_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_3174_, v_as_3175_, v_lo_3176_, v_hi_3177_, v_w_3178_, v_hlo_3179_, v_hhi_3180_);
lean_dec(v_hi_3177_);
lean_dec(v_n_3174_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_3182_, lean_object* v_x_3183_, lean_object* v_x_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3183_, v_x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3186_, lean_object* v_x_3187_, lean_object* v_x_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_3186_, v_x_3187_, v_x_3188_);
lean_dec(v_x_3188_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3190_, v___y_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b2_3200_, lean_object* v_k_3201_, lean_object* v_v_3202_, lean_object* v_t_3203_, lean_object* v_hl_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_3201_, v_v_3202_, v_t_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_as_3206_, lean_object* v_as_x27_3207_, lean_object* v_b_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_as_x27_3207_, v_b_3208_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_as_3211_, lean_object* v_as_x27_3212_, lean_object* v_b_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_as_3211_, v_as_x27_3212_, v_b_3213_, v_a_3214_);
lean_dec(v_as_3211_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_00_u03b4_3216_, lean_object* v_t_3217_, lean_object* v_k_3218_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_3217_, v_k_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___boxed(lean_object* v_00_u03b4_3220_, lean_object* v_t_3221_, lean_object* v_k_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v_00_u03b4_3220_, v_t_3221_, v_k_3222_);
lean_dec(v_k_3222_);
lean_dec(v_t_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(lean_object* v_00_u03b2_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_3225_, v_x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___boxed(lean_object* v_00_u03b2_3228_, lean_object* v_x_3229_, lean_object* v_x_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(v_00_u03b2_3228_, v_x_3229_, v_x_3230_);
lean_dec(v_x_3230_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3232_, size_t v_sz_3233_, size_t v_i_3234_, lean_object* v_b_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_as_3232_, v_sz_3233_, v_i_3234_, v_b_3235_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3240_, lean_object* v_sz_3241_, lean_object* v_i_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
size_t v_sz_boxed_3247_; size_t v_i_boxed_3248_; lean_object* v_res_3249_; 
v_sz_boxed_3247_ = lean_unbox_usize(v_sz_3241_);
lean_dec(v_sz_3241_);
v_i_boxed_3248_ = lean_unbox_usize(v_i_3242_);
lean_dec(v_i_3242_);
v_res_3249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3240_, v_sz_boxed_3247_, v_i_boxed_3248_, v_b_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v_as_3240_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_init_3250_, lean_object* v_t_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_3250_, v_t_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_init_3253_, lean_object* v_t_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_init_3253_, v_t_3254_);
lean_dec(v_t_3254_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_n_3256_, lean_object* v_as_3257_, lean_object* v_lo_3258_, lean_object* v_hi_3259_, lean_object* v_w_3260_, lean_object* v_hlo_3261_, lean_object* v_hhi_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_as_3257_, v_lo_3258_, v_hi_3259_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_n_3264_, lean_object* v_as_3265_, lean_object* v_lo_3266_, lean_object* v_hi_3267_, lean_object* v_w_3268_, lean_object* v_hlo_3269_, lean_object* v_hhi_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_n_3264_, v_as_3265_, v_lo_3266_, v_hi_3267_, v_w_3268_, v_hlo_3269_, v_hhi_3270_);
lean_dec(v_hi_3267_);
lean_dec(v_n_3264_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object* v_init_3272_, lean_object* v_x_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_3272_, v_x_3273_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object* v_init_3278_, lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(v_init_3278_, v_x_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3284_, lean_object* v_x_3285_, size_t v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3285_, v_x_3286_, v_x_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_, lean_object* v_x_3292_){
_start:
{
size_t v_x_20670__boxed_3293_; lean_object* v_res_3294_; 
v_x_20670__boxed_3293_ = lean_unbox_usize(v_x_3291_);
lean_dec(v_x_3291_);
v_res_3294_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3289_, v_x_3290_, v_x_20670__boxed_3293_, v_x_3292_);
lean_dec(v_x_3292_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3295_, lean_object* v_k_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3295_, v_k_3296_, v_x_3297_, v_x_3298_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3301_, lean_object* v_k_3302_, lean_object* v_x_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3301_, v_k_3302_, v_x_3303_, v_x_3304_, v_x_3305_);
lean_dec_ref(v_k_3302_);
lean_dec_ref(v_as_3301_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object* v_00_u03b2_3307_, lean_object* v_m_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_3308_, v_a_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object* v_00_u03b2_3311_, lean_object* v_m_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(v_00_u03b2_3311_, v_m_3312_, v_a_3313_);
lean_dec(v_a_3313_);
lean_dec_ref(v_m_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3315_, lean_object* v_keys_3316_, lean_object* v_vals_3317_, lean_object* v_heq_3318_, lean_object* v_i_3319_, lean_object* v_k_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3316_, v_vals_3317_, v_i_3319_, v_k_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3322_, lean_object* v_keys_3323_, lean_object* v_vals_3324_, lean_object* v_heq_3325_, lean_object* v_i_3326_, lean_object* v_k_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3322_, v_keys_3323_, v_vals_3324_, v_heq_3325_, v_i_3326_, v_k_3327_);
lean_dec(v_k_3327_);
lean_dec_ref(v_vals_3324_);
lean_dec_ref(v_keys_3323_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object* v_00_u03b2_3329_, lean_object* v_a_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_3330_, v_x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object* v_00_u03b2_3333_, lean_object* v_a_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(v_00_u03b2_3333_, v_a_3334_, v_x_3335_);
lean_dec(v_x_3335_);
lean_dec(v_a_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3351_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3352_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3353_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3354_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3355_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3351_, v___x_3352_, v___x_3353_, v___x_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3361_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3362_ = l_Lean_addBuiltinDocString(v___x_3360_, v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3392_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3393_ = l_Lean_addBuiltinDeclarationRanges(v___x_3391_, v___x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, uint8_t v_includeUnnamed_3399_, lean_object* v_x_3400_, lean_object* v_____s_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_fst_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3460_; 
v_fst_3407_ = lean_ctor_get(v_x_3400_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_x_3400_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v_x_3400_, 1);
lean_dec(v_unused_3461_);
v___x_3409_ = v_x_3400_;
v_isShared_3410_ = v_isSharedCheck_3460_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_fst_3407_);
lean_dec(v_x_3400_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3460_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v_userName_3412_; lean_object* v___y_3413_; lean_object* v___x_3445_; 
lean_inc(v_fst_3407_);
lean_inc_ref(v_env_3396_);
v___x_3445_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3396_, v_fst_3407_);
if (lean_obj_tag(v___x_3445_) == 1)
{
lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3453_; 
lean_del_object(v___x_3409_);
lean_dec(v_fst_3407_);
lean_dec_ref(v_env_3396_);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3453_ == 0)
{
lean_object* v_unused_3454_; 
v_unused_3454_ = lean_ctor_get(v___x_3445_, 0);
lean_dec(v_unused_3454_);
v___x_3447_ = v___x_3445_;
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
else
{
lean_dec(v___x_3445_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3453_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v_____s_3401_);
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_____s_3401_);
v___x_3450_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
}
else
{
lean_object* v___x_3455_; 
lean_dec(v___x_3445_);
v___x_3455_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_a_3398_, v_fst_3407_);
if (lean_obj_tag(v___x_3455_) == 1)
{
lean_object* v_val_3456_; 
v_val_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_val_3456_);
lean_dec_ref(v___x_3455_);
v_userName_3412_ = v_val_3456_;
v___y_3413_ = v___y_3404_;
goto v___jp_3411_;
}
else
{
lean_dec(v___x_3455_);
if (v_includeUnnamed_3399_ == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_del_object(v___x_3409_);
lean_dec(v_fst_3407_);
lean_dec_ref(v_env_3396_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v_____s_3401_);
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
else
{
lean_object* v___x_3459_; 
lean_inc(v_fst_3407_);
v___x_3459_ = l_Lean_Name_toString(v_fst_3407_, v_includeUnnamed_3399_);
v_userName_3412_ = v___x_3459_;
v___y_3413_ = v___y_3404_;
goto v___jp_3411_;
}
}
}
v___jp_3411_:
{
uint8_t v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = 1;
lean_inc(v_fst_3407_);
lean_inc_ref(v_env_3396_);
v___x_3415_ = l_Lean_findDocString_x3f(v_env_3396_, v_fst_3407_, v___x_3414_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3429_; 
lean_del_object(v___x_3409_);
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3429_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3429_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3420_ = l_Lean_NameSet_empty;
v___x_3421_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3397_, v_fst_3407_, v___x_3420_);
lean_inc(v_fst_3407_);
v___x_3422_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3396_, v_fst_3407_);
v___x_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3423_, 0, v_fst_3407_);
lean_ctor_set(v___x_3423_, 1, v_userName_3412_);
lean_ctor_set(v___x_3423_, 2, v___x_3421_);
lean_ctor_set(v___x_3423_, 3, v_a_3416_);
lean_ctor_set(v___x_3423_, 4, v___x_3422_);
v___x_3424_ = lean_array_push(v_____s_3401_, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3425_);
v___x_3427_ = v___x_3418_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3444_; 
lean_dec_ref(v_userName_3412_);
lean_dec(v_fst_3407_);
lean_dec_ref(v_____s_3401_);
lean_dec_ref(v_env_3396_);
v_a_3430_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3432_ = v___x_3415_;
v_isShared_3433_ = v_isSharedCheck_3444_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3415_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3444_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_ref_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3439_; 
v_ref_3434_ = lean_ctor_get(v___y_3413_, 5);
v___x_3435_ = lean_io_error_to_string(v_a_3430_);
v___x_3436_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
v___x_3437_ = l_Lean_MessageData_ofFormat(v___x_3436_);
lean_inc(v_ref_3434_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 1, v___x_3437_);
lean_ctor_set(v___x_3409_, 0, v_ref_3434_);
v___x_3439_ = v___x_3409_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_ref_3434_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3441_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v___x_3439_);
v___x_3441_ = v___x_3432_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_includeUnnamed_3465_, lean_object* v_x_3466_, lean_object* v_____s_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
uint8_t v_includeUnnamed_boxed_3473_; lean_object* v_res_3474_; 
v_includeUnnamed_boxed_3473_ = lean_unbox(v_includeUnnamed_3465_);
v_res_3474_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3462_, v_a_3463_, v_a_3464_, v_includeUnnamed_boxed_3473_, v_x_3466_, v_____s_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v_a_3464_);
lean_dec(v_a_3463_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3475_, size_t v_sz_3476_, size_t v_i_3477_, lean_object* v_b_3478_){
_start:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_usize_dec_lt(v_i_3477_, v_sz_3476_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_b_3478_);
return v___x_3481_;
}
else
{
lean_object* v_a_3482_; lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; size_t v___x_3489_; size_t v___x_3490_; 
v_a_3482_ = lean_array_uget_borrowed(v_as_3475_, v_i_3477_);
v_fst_3483_ = lean_ctor_get(v_a_3482_, 0);
v_snd_3484_ = lean_ctor_get(v_a_3482_, 1);
v___x_3485_ = l_Lean_NameSet_empty;
v___x_3486_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3478_, v_fst_3483_, v___x_3485_);
lean_inc(v_snd_3484_);
v___x_3487_ = l_Lean_NameSet_insert(v___x_3486_, v_snd_3484_);
lean_inc(v_fst_3483_);
v___x_3488_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3483_, v___x_3487_, v_b_3478_);
v___x_3489_ = ((size_t)1ULL);
v___x_3490_ = lean_usize_add(v_i_3477_, v___x_3489_);
v_i_3477_ = v___x_3490_;
v_b_3478_ = v___x_3488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3492_, lean_object* v_sz_3493_, lean_object* v_i_3494_, lean_object* v_b_3495_, lean_object* v___y_3496_){
_start:
{
size_t v_sz_boxed_3497_; size_t v_i_boxed_3498_; lean_object* v_res_3499_; 
v_sz_boxed_3497_ = lean_unbox_usize(v_sz_3493_);
lean_dec(v_sz_3493_);
v_i_boxed_3498_ = lean_unbox_usize(v_i_3494_);
lean_dec(v_i_3494_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3492_, v_sz_boxed_3497_, v_i_boxed_3498_, v_b_3495_);
lean_dec_ref(v_as_3492_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3500_, size_t v_sz_3501_, size_t v_i_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
uint8_t v___x_3509_; 
v___x_3509_ = lean_usize_dec_lt(v_i_3502_, v_sz_3501_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; 
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_b_3503_);
return v___x_3510_;
}
else
{
lean_object* v_a_3511_; size_t v_sz_3512_; size_t v___x_3513_; lean_object* v___x_3514_; 
v_a_3511_ = lean_array_uget_borrowed(v_as_3500_, v_i_3502_);
v_sz_3512_ = lean_array_size(v_a_3511_);
v___x_3513_ = ((size_t)0ULL);
v___x_3514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3511_, v_sz_3512_, v___x_3513_, v_b_3503_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; size_t v___x_3516_; size_t v___x_3517_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref(v___x_3514_);
v___x_3516_ = ((size_t)1ULL);
v___x_3517_ = lean_usize_add(v_i_3502_, v___x_3516_);
v_i_3502_ = v___x_3517_;
v_b_3503_ = v_a_3515_;
goto _start;
}
else
{
return v___x_3514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3519_, lean_object* v_sz_3520_, lean_object* v_i_3521_, lean_object* v_b_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
size_t v_sz_boxed_3528_; size_t v_i_boxed_3529_; lean_object* v_res_3530_; 
v_sz_boxed_3528_ = lean_unbox_usize(v_sz_3520_);
lean_dec(v_sz_3520_);
v_i_boxed_3529_ = lean_unbox_usize(v_i_3521_);
lean_dec(v_i_3521_);
v_res_3530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3519_, v_sz_boxed_3528_, v_i_boxed_3529_, v_b_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v_as_3519_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3531_, lean_object* v_keys_3532_, lean_object* v_vals_3533_, lean_object* v_i_3534_, lean_object* v_acc_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3541_ = lean_array_get_size(v_keys_3532_);
v___x_3542_ = lean_nat_dec_lt(v_i_3534_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v_i_3534_);
lean_dec_ref(v_f_3531_);
v___x_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3543_, 0, v_acc_3535_);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
else
{
lean_object* v_k_3545_; lean_object* v_v_3546_; lean_object* v___x_3547_; 
v_k_3545_ = lean_array_fget_borrowed(v_keys_3532_, v_i_3534_);
v_v_3546_ = lean_array_fget_borrowed(v_vals_3533_, v_i_3534_);
lean_inc_ref(v_f_3531_);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3538_);
lean_inc(v___y_3537_);
lean_inc_ref(v___y_3536_);
lean_inc(v_v_3546_);
lean_inc(v_k_3545_);
v___x_3547_ = lean_apply_8(v_f_3531_, v_acc_3535_, v_k_3545_, v_v_3546_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, lean_box(0));
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
if (lean_obj_tag(v_a_3548_) == 0)
{
lean_dec_ref(v_a_3548_);
lean_dec(v_i_3534_);
lean_dec_ref(v_f_3531_);
return v___x_3547_;
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec_ref(v___x_3547_);
v_a_3549_ = lean_ctor_get(v_a_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref(v_a_3548_);
v___x_3550_ = lean_unsigned_to_nat(1u);
v___x_3551_ = lean_nat_add(v_i_3534_, v___x_3550_);
lean_dec(v_i_3534_);
v_i_3534_ = v___x_3551_;
v_acc_3535_ = v_a_3549_;
goto _start;
}
}
else
{
lean_dec(v_i_3534_);
lean_dec_ref(v_f_3531_);
return v___x_3547_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3553_, lean_object* v_keys_3554_, lean_object* v_vals_3555_, lean_object* v_i_3556_, lean_object* v_acc_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3553_, v_keys_3554_, v_vals_3555_, v_i_3556_, v_acc_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v_vals_3555_);
lean_dec_ref(v_keys_3554_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3564_, lean_object* v_x_3565_, lean_object* v_x_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_object* v_es_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3594_; 
v_es_3572_ = lean_ctor_get(v_x_3565_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_x_3565_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3574_ = v_x_3565_;
v_isShared_3575_ = v_isSharedCheck_3594_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_es_3572_);
lean_dec(v_x_3565_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3594_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3576_ = lean_unsigned_to_nat(0u);
v___x_3577_ = lean_array_get_size(v_es_3572_);
v___x_3578_ = lean_nat_dec_lt(v___x_3576_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3580_; 
lean_dec_ref(v_es_3572_);
lean_dec_ref(v_f_3564_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 1);
lean_ctor_set(v___x_3574_, 0, v_x_3566_);
v___x_3580_ = v___x_3574_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_x_3566_);
v___x_3580_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
else
{
uint8_t v___x_3583_; 
v___x_3583_ = lean_nat_dec_le(v___x_3577_, v___x_3577_);
if (v___x_3583_ == 0)
{
if (v___x_3578_ == 0)
{
lean_object* v___x_3585_; 
lean_dec_ref(v_es_3572_);
lean_dec_ref(v_f_3564_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 1);
lean_ctor_set(v___x_3574_, 0, v_x_3566_);
v___x_3585_ = v___x_3574_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_x_3566_);
v___x_3585_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
return v___x_3586_;
}
}
else
{
size_t v___x_3588_; size_t v___x_3589_; lean_object* v___x_3590_; 
lean_del_object(v___x_3574_);
v___x_3588_ = ((size_t)0ULL);
v___x_3589_ = lean_usize_of_nat(v___x_3577_);
v___x_3590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3564_, v_es_3572_, v___x_3588_, v___x_3589_, v_x_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec_ref(v_es_3572_);
return v___x_3590_;
}
}
else
{
size_t v___x_3591_; size_t v___x_3592_; lean_object* v___x_3593_; 
lean_del_object(v___x_3574_);
v___x_3591_ = ((size_t)0ULL);
v___x_3592_ = lean_usize_of_nat(v___x_3577_);
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3564_, v_es_3572_, v___x_3591_, v___x_3592_, v_x_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec_ref(v_es_3572_);
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_ks_3595_; lean_object* v_vs_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_ks_3595_ = lean_ctor_get(v_x_3565_, 0);
lean_inc_ref(v_ks_3595_);
v_vs_3596_ = lean_ctor_get(v_x_3565_, 1);
lean_inc_ref(v_vs_3596_);
lean_dec_ref(v_x_3565_);
v___x_3597_ = lean_unsigned_to_nat(0u);
v___x_3598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3564_, v_ks_3595_, v_vs_3596_, v___x_3597_, v_x_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec_ref(v_vs_3596_);
lean_dec_ref(v_ks_3595_);
return v___x_3598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3599_, lean_object* v_as_3600_, size_t v_i_3601_, size_t v_stop_3602_, lean_object* v_b_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_a_3610_; lean_object* v___y_3615_; uint8_t v___x_3618_; 
v___x_3618_ = lean_usize_dec_eq(v_i_3601_, v_stop_3602_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_array_uget_borrowed(v_as_3600_, v_i_3601_);
switch(lean_obj_tag(v___x_3619_))
{
case 0:
{
lean_object* v_key_3620_; lean_object* v_val_3621_; lean_object* v___x_3622_; 
v_key_3620_ = lean_ctor_get(v___x_3619_, 0);
v_val_3621_ = lean_ctor_get(v___x_3619_, 1);
lean_inc_ref(v_f_3599_);
lean_inc(v___y_3607_);
lean_inc_ref(v___y_3606_);
lean_inc(v___y_3605_);
lean_inc_ref(v___y_3604_);
lean_inc(v_val_3621_);
lean_inc(v_key_3620_);
v___x_3622_ = lean_apply_8(v_f_3599_, v_b_3603_, v_key_3620_, v_val_3621_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, lean_box(0));
v___y_3615_ = v___x_3622_;
goto v___jp_3614_;
}
case 1:
{
lean_object* v_node_3623_; lean_object* v___x_3624_; 
v_node_3623_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_node_3623_);
lean_inc_ref(v_f_3599_);
v___x_3624_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3599_, v_node_3623_, v_b_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
v___y_3615_ = v___x_3624_;
goto v___jp_3614_;
}
default: 
{
v_a_3610_ = v_b_3603_;
goto v___jp_3609_;
}
}
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_dec_ref(v_f_3599_);
v___x_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3625_, 0, v_b_3603_);
v___x_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
return v___x_3626_;
}
v___jp_3609_:
{
size_t v___x_3611_; size_t v___x_3612_; 
v___x_3611_ = ((size_t)1ULL);
v___x_3612_ = lean_usize_add(v_i_3601_, v___x_3611_);
v_i_3601_ = v___x_3612_;
v_b_3603_ = v_a_3610_;
goto _start;
}
v___jp_3614_:
{
if (lean_obj_tag(v___y_3615_) == 0)
{
lean_object* v_a_3616_; 
v_a_3616_ = lean_ctor_get(v___y_3615_, 0);
if (lean_obj_tag(v_a_3616_) == 0)
{
lean_dec_ref(v_f_3599_);
return v___y_3615_;
}
else
{
lean_object* v_a_3617_; 
lean_inc_ref(v_a_3616_);
lean_dec_ref(v___y_3615_);
v_a_3617_ = lean_ctor_get(v_a_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref(v_a_3616_);
v_a_3610_ = v_a_3617_;
goto v___jp_3609_;
}
}
else
{
lean_dec_ref(v_f_3599_);
return v___y_3615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3627_, lean_object* v_as_3628_, lean_object* v_i_3629_, lean_object* v_stop_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
size_t v_i_boxed_3637_; size_t v_stop_boxed_3638_; lean_object* v_res_3639_; 
v_i_boxed_3637_ = lean_unbox_usize(v_i_3629_);
lean_dec(v_i_3629_);
v_stop_boxed_3638_ = lean_unbox_usize(v_stop_3630_);
lean_dec(v_stop_3630_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3627_, v_as_3628_, v_i_boxed_3637_, v_stop_boxed_3638_, v_b_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_as_3628_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3640_, v_x_3641_, v_x_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3649_, lean_object* v_s_3650_, lean_object* v_a_3651_, lean_object* v_b_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v_a_3651_);
lean_ctor_set(v___x_3658_, 1, v_b_3652_);
lean_inc(v___y_3656_);
lean_inc_ref(v___y_3655_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
v___x_3659_ = lean_apply_7(v_f_3649_, v___x_3658_, v_s_3650_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, lean_box(0));
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3686_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3686_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3686_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
if (lean_obj_tag(v_a_3660_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3674_; 
v_a_3664_ = lean_ctor_get(v_a_3660_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_a_3660_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3666_ = v_a_3660_;
v_isShared_3667_ = v_isSharedCheck_3674_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v_a_3660_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3674_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3669_);
v___x_3671_ = v___x_3662_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3685_; 
v_a_3675_ = lean_ctor_get(v_a_3660_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_a_3660_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3677_ = v_a_3660_;
v_isShared_3678_ = v_isSharedCheck_3685_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v_a_3660_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3685_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3682_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3680_);
v___x_3682_ = v___x_3662_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
v_a_3687_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3659_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3659_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3695_, lean_object* v_s_3696_, lean_object* v_a_3697_, lean_object* v_b_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3695_, v_s_3696_, v_a_3697_, v_b_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3705_, lean_object* v_init_3706_, lean_object* v_f_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v___f_3713_; lean_object* v___x_3714_; 
v___f_3713_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3713_, 0, v_f_3707_);
v___x_3714_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3713_, v_map_3705_, v_init_3706_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3723_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3723_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3723_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v_a_3719_; lean_object* v___x_3721_; 
v_a_3719_ = lean_ctor_get(v_a_3715_, 0);
lean_inc(v_a_3719_);
lean_dec(v_a_3715_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v_a_3719_);
v___x_3721_ = v___x_3717_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
v_a_3724_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3714_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3714_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3732_, lean_object* v_init_3733_, lean_object* v_f_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3732_, v_init_3733_, v_f_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3743_; lean_object* v_env_3744_; lean_object* v___x_3745_; lean_object* v_ext_3746_; lean_object* v_toEnvExtension_3747_; lean_object* v_asyncMode_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v_categories_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3743_ = lean_st_ref_get(v___y_3741_);
v_env_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc_ref(v_env_3744_);
lean_dec(v___x_3743_);
v___x_3745_ = l_Lean_Parser_parserExtension;
v_ext_3746_ = lean_ctor_get(v___x_3745_, 1);
lean_inc_ref(v_ext_3746_);
v_toEnvExtension_3747_ = lean_ctor_get(v_ext_3746_, 0);
lean_inc_ref(v_toEnvExtension_3747_);
lean_dec_ref(v_ext_3746_);
v_asyncMode_3748_ = lean_ctor_get(v_toEnvExtension_3747_, 2);
lean_inc(v_asyncMode_3748_);
lean_dec_ref(v_toEnvExtension_3747_);
v___x_3749_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3744_);
v___x_3750_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3749_, v___x_3745_, v_env_3744_, v_asyncMode_3748_);
lean_dec(v_asyncMode_3748_);
v_categories_3751_ = lean_ctor_get(v___x_3750_, 2);
lean_inc_ref(v_categories_3751_);
lean_dec(v___x_3750_);
v___x_3752_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3753_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3751_, v___x_3752_);
if (lean_obj_tag(v___x_3753_) == 1)
{
lean_object* v_val_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3792_; 
v_val_3754_ = lean_ctor_get(v___x_3753_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3756_ = v___x_3753_;
v_isShared_3757_ = v_isSharedCheck_3792_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_val_3754_);
lean_dec(v___x_3753_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3792_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___y_3759_; lean_object* v___x_3768_; lean_object* v_toEnvExtension_3769_; lean_object* v_exportEntriesFn_3770_; lean_object* v_asyncMode_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v_importedEntries_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3768_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc_ref(v_toEnvExtension_3769_);
v_exportEntriesFn_3770_ = lean_ctor_get(v___x_3768_, 4);
lean_inc_ref(v_exportEntriesFn_3770_);
v_asyncMode_3771_ = lean_ctor_get(v_toEnvExtension_3769_, 2);
lean_inc(v_asyncMode_3771_);
v___x_3772_ = lean_box(1);
v___x_3773_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3774_ = lean_box(0);
lean_inc_ref(v_env_3744_);
v___x_3775_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3773_, v_toEnvExtension_3769_, v_env_3744_, v_asyncMode_3771_, v___x_3774_);
lean_dec_ref(v_toEnvExtension_3769_);
v_importedEntries_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc_ref(v_importedEntries_3776_);
lean_dec(v___x_3775_);
lean_inc_ref(v_env_3744_);
v___x_3777_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3772_, v___x_3768_, v_env_3744_, v_asyncMode_3771_, v___x_3774_);
lean_dec(v_asyncMode_3771_);
v___x_3778_ = 0;
v___x_3779_ = lean_box(v___x_3778_);
v___x_3780_ = lean_apply_3(v_exportEntriesFn_3770_, v_env_3744_, v___x_3777_, v___x_3779_);
v___x_3781_ = lean_array_push(v_importedEntries_3776_, v___x_3780_);
v___x_3782_ = lean_unsigned_to_nat(0u);
v___x_3783_ = lean_array_get_size(v___x_3781_);
v___x_3784_ = lean_nat_dec_lt(v___x_3782_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_dec_ref(v___x_3781_);
v___y_3759_ = v___x_3772_;
goto v___jp_3758_;
}
else
{
uint8_t v___x_3785_; 
v___x_3785_ = lean_nat_dec_le(v___x_3783_, v___x_3783_);
if (v___x_3785_ == 0)
{
if (v___x_3784_ == 0)
{
lean_dec_ref(v___x_3781_);
v___y_3759_ = v___x_3772_;
goto v___jp_3758_;
}
else
{
size_t v___x_3786_; size_t v___x_3787_; lean_object* v___x_3788_; 
v___x_3786_ = ((size_t)0ULL);
v___x_3787_ = lean_usize_of_nat(v___x_3783_);
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3781_, v___x_3786_, v___x_3787_, v___x_3772_);
lean_dec_ref(v___x_3781_);
v___y_3759_ = v___x_3788_;
goto v___jp_3758_;
}
}
else
{
size_t v___x_3789_; size_t v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = ((size_t)0ULL);
v___x_3790_ = lean_usize_of_nat(v___x_3783_);
v___x_3791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3781_, v___x_3789_, v___x_3790_, v___x_3772_);
lean_dec_ref(v___x_3781_);
v___y_3759_ = v___x_3791_;
goto v___jp_3758_;
}
}
v___jp_3758_:
{
lean_object* v_tables_3760_; lean_object* v_leadingTable_3761_; lean_object* v_trailingTable_3762_; lean_object* v_firstTokens_3763_; lean_object* v_firstTokens_3764_; lean_object* v___x_3766_; 
v_tables_3760_ = lean_ctor_get(v_val_3754_, 2);
v_leadingTable_3761_ = lean_ctor_get(v_tables_3760_, 0);
v_trailingTable_3762_ = lean_ctor_get(v_tables_3760_, 2);
lean_inc(v_trailingTable_3762_);
lean_inc(v_leadingTable_3761_);
lean_inc(v_val_3754_);
v_firstTokens_3763_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3754_, v_leadingTable_3761_, v___y_3759_);
v_firstTokens_3764_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3754_, v_trailingTable_3762_, v_firstTokens_3763_);
if (v_isShared_3757_ == 0)
{
lean_ctor_set_tag(v___x_3756_, 0);
lean_ctor_set(v___x_3756_, 0, v_firstTokens_3764_);
v___x_3766_ = v___x_3756_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_firstTokens_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
lean_dec(v___x_3753_);
lean_dec_ref(v_env_3744_);
v___x_3793_ = lean_box(1);
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3795_);
lean_dec(v___y_3795_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v___x_3806_; lean_object* v_env_3807_; lean_object* v___x_3808_; lean_object* v_toEnvExtension_3809_; lean_object* v_exportEntriesFn_3810_; lean_object* v_asyncMode_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v_importedEntries_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; size_t v_sz_3822_; size_t v___x_3823_; lean_object* v___x_3824_; 
v___x_3806_ = lean_st_ref_get(v_a_3804_);
v_env_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc_ref(v_env_3807_);
lean_dec(v___x_3806_);
v___x_3808_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc_ref(v_toEnvExtension_3809_);
v_exportEntriesFn_3810_ = lean_ctor_get(v___x_3808_, 4);
lean_inc_ref(v_exportEntriesFn_3810_);
v_asyncMode_3811_ = lean_ctor_get(v_toEnvExtension_3809_, 2);
lean_inc(v_asyncMode_3811_);
v___x_3812_ = lean_box(1);
v___x_3813_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3814_ = lean_box(0);
lean_inc_ref(v_env_3807_);
v___x_3815_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3813_, v_toEnvExtension_3809_, v_env_3807_, v_asyncMode_3811_, v___x_3814_);
lean_dec_ref(v_toEnvExtension_3809_);
v_importedEntries_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc_ref(v_importedEntries_3816_);
lean_dec(v___x_3815_);
lean_inc_ref(v_env_3807_);
v___x_3817_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3812_, v___x_3808_, v_env_3807_, v_asyncMode_3811_, v___x_3814_);
lean_dec(v_asyncMode_3811_);
v___x_3818_ = 0;
v___x_3819_ = lean_box(v___x_3818_);
lean_inc_ref(v_env_3807_);
v___x_3820_ = lean_apply_3(v_exportEntriesFn_3810_, v_env_3807_, v___x_3817_, v___x_3819_);
v___x_3821_ = lean_array_push(v_importedEntries_3816_, v___x_3820_);
v_sz_3822_ = lean_array_size(v___x_3821_);
v___x_3823_ = ((size_t)0ULL);
v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3821_, v_sz_3822_, v___x_3823_, v___x_3812_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_);
lean_dec_ref(v___x_3821_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3849_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3849_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3849_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v_ext_3830_; lean_object* v_toEnvExtension_3831_; lean_object* v_asyncMode_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v_categories_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3829_ = l_Lean_Parser_parserExtension;
v_ext_3830_ = lean_ctor_get(v___x_3829_, 1);
lean_inc_ref(v_ext_3830_);
v_toEnvExtension_3831_ = lean_ctor_get(v_ext_3830_, 0);
lean_inc_ref(v_toEnvExtension_3831_);
lean_dec_ref(v_ext_3830_);
v_asyncMode_3832_ = lean_ctor_get(v_toEnvExtension_3831_, 2);
lean_inc(v_asyncMode_3832_);
lean_dec_ref(v_toEnvExtension_3831_);
v___x_3833_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3807_);
v___x_3834_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3833_, v___x_3829_, v_env_3807_, v_asyncMode_3832_);
lean_dec(v_asyncMode_3832_);
v_categories_3835_ = lean_ctor_get(v___x_3834_, 2);
lean_inc_ref(v_categories_3835_);
lean_dec(v___x_3834_);
v___x_3836_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3837_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3838_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3835_, v___x_3837_);
if (lean_obj_tag(v___x_3838_) == 1)
{
lean_object* v_val_3839_; lean_object* v___x_3840_; lean_object* v_a_3841_; lean_object* v_kinds_3842_; lean_object* v___x_3843_; lean_object* v___f_3844_; lean_object* v___x_3845_; 
lean_del_object(v___x_3827_);
v_val_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_val_3839_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3804_);
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref(v___x_3840_);
v_kinds_3842_ = lean_ctor_get(v_val_3839_, 1);
lean_inc_ref(v_kinds_3842_);
lean_dec(v_val_3839_);
v___x_3843_ = lean_box(v_includeUnnamed_3800_);
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3844_, 0, v_env_3807_);
lean_closure_set(v___f_3844_, 1, v_a_3825_);
lean_closure_set(v___f_3844_, 2, v_a_3841_);
lean_closure_set(v___f_3844_, 3, v___x_3843_);
v___x_3845_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3842_, v___x_3836_, v___f_3844_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_);
return v___x_3845_;
}
else
{
lean_object* v___x_3847_; 
lean_dec(v___x_3838_);
lean_dec(v_a_3825_);
lean_dec_ref(v_env_3807_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3836_);
v___x_3847_ = v___x_3827_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3836_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v_env_3807_);
v_a_3850_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3824_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3824_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
uint8_t v_includeUnnamed_boxed_3864_; lean_object* v_res_3865_; 
v_includeUnnamed_boxed_3864_ = lean_unbox(v_includeUnnamed_3858_);
v_res_3865_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3864_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3866_, size_t v_sz_3867_, size_t v_i_3868_, lean_object* v_b_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3866_, v_sz_3867_, v_i_3868_, v_b_3869_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3876_, lean_object* v_sz_3877_, lean_object* v_i_3878_, lean_object* v_b_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
size_t v_sz_boxed_3885_; size_t v_i_boxed_3886_; lean_object* v_res_3887_; 
v_sz_boxed_3885_ = lean_unbox_usize(v_sz_3877_);
lean_dec(v_sz_3877_);
v_i_boxed_3886_ = lean_unbox_usize(v_i_3878_);
lean_dec(v_i_3878_);
v_res_3887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3876_, v_sz_boxed_3885_, v_i_boxed_3886_, v_b_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec_ref(v_as_3876_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3891_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3900_, lean_object* v_00_u03b2_3901_, lean_object* v_map_3902_, lean_object* v_init_3903_, lean_object* v_f_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3902_, v_init_3903_, v_f_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3911_, lean_object* v_00_u03b2_3912_, lean_object* v_map_3913_, lean_object* v_init_3914_, lean_object* v_f_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3911_, v_00_u03b2_3912_, v_map_3913_, v_init_3914_, v_f_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3922_, lean_object* v_f_3923_, lean_object* v_init_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3923_, v_map_3922_, v_init_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3931_, lean_object* v_f_3932_, lean_object* v_init_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3931_, v_f_3932_, v_init_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3940_, lean_object* v_00_u03c3_3941_, lean_object* v_00_u03b2_3942_, lean_object* v_map_3943_, lean_object* v_f_3944_, lean_object* v_init_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3944_, v_map_3943_, v_init_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3952_, lean_object* v_00_u03c3_3953_, lean_object* v_00_u03b2_3954_, lean_object* v_map_3955_, lean_object* v_f_3956_, lean_object* v_init_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3952_, v_00_u03c3_3953_, v_00_u03b2_3954_, v_map_3955_, v_f_3956_, v_init_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3964_, lean_object* v_00_u03c3_3965_, lean_object* v_00_u03b1_3966_, lean_object* v_00_u03b2_3967_, lean_object* v_f_3968_, lean_object* v_x_3969_, lean_object* v_x_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3968_, v_x_3969_, v_x_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3977_, lean_object* v_00_u03c3_3978_, lean_object* v_00_u03b1_3979_, lean_object* v_00_u03b2_3980_, lean_object* v_f_3981_, lean_object* v_x_3982_, lean_object* v_x_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3977_, v_00_u03c3_3978_, v_00_u03b1_3979_, v_00_u03b2_3980_, v_f_3981_, v_x_3982_, v_x_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3990_, lean_object* v_00_u03b2_3991_, lean_object* v_00_u03c3_3992_, lean_object* v_00_u03c3_3993_, lean_object* v_f_3994_, lean_object* v_as_3995_, size_t v_i_3996_, size_t v_stop_3997_, lean_object* v_b_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3994_, v_as_3995_, v_i_3996_, v_stop_3997_, v_b_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4005_, lean_object* v_00_u03b2_4006_, lean_object* v_00_u03c3_4007_, lean_object* v_00_u03c3_4008_, lean_object* v_f_4009_, lean_object* v_as_4010_, lean_object* v_i_4011_, lean_object* v_stop_4012_, lean_object* v_b_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
size_t v_i_boxed_4019_; size_t v_stop_boxed_4020_; lean_object* v_res_4021_; 
v_i_boxed_4019_ = lean_unbox_usize(v_i_4011_);
lean_dec(v_i_4011_);
v_stop_boxed_4020_ = lean_unbox_usize(v_stop_4012_);
lean_dec(v_stop_4012_);
v_res_4021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_4005_, v_00_u03b2_4006_, v_00_u03c3_4007_, v_00_u03c3_4008_, v_f_4009_, v_as_4010_, v_i_boxed_4019_, v_stop_boxed_4020_, v_b_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec_ref(v_as_4010_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_4022_, lean_object* v_00_u03c3_4023_, lean_object* v_00_u03b1_4024_, lean_object* v_00_u03b2_4025_, lean_object* v_f_4026_, lean_object* v_keys_4027_, lean_object* v_vals_4028_, lean_object* v_heq_4029_, lean_object* v_i_4030_, lean_object* v_acc_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4026_, v_keys_4027_, v_vals_4028_, v_i_4030_, v_acc_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_4038_, lean_object* v_00_u03c3_4039_, lean_object* v_00_u03b1_4040_, lean_object* v_00_u03b2_4041_, lean_object* v_f_4042_, lean_object* v_keys_4043_, lean_object* v_vals_4044_, lean_object* v_heq_4045_, lean_object* v_i_4046_, lean_object* v_acc_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_4038_, v_00_u03c3_4039_, v_00_u03b1_4040_, v_00_u03b2_4041_, v_f_4042_, v_keys_4043_, v_vals_4044_, v_heq_4045_, v_i_4046_, v_acc_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v_vals_4044_);
lean_dec_ref(v_keys_4043_);
return v_res_4053_;
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
res = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
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
