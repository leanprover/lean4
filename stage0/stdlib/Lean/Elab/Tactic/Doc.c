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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_156_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
lean_inc(v_macroStack_153_);
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
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_343_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_343_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_343_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_343_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___y_281_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___x_330_; lean_object* v_env_331_; lean_object* v___x_332_; 
v___x_330_ = lean_st_ref_get(v_a_249_);
v_env_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_env_331_);
lean_dec(v___x_330_);
lean_inc(v_a_276_);
v___x_332_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_331_, v_a_276_);
if (lean_obj_tag(v___x_332_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v_val_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_val_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_335_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = l_Lean_MessageData_ofConstName(v_val_333_, v___x_257_);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_334_);
v___x_342_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_341_, v_a_248_, v_a_249_);
lean_dec(v___x_268_);
return v___x_342_;
}
else
{
lean_dec(v___x_332_);
v___y_325_ = v_a_248_;
v___y_326_ = v_a_249_;
goto v___jp_324_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v_messages_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v_newDecls_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_313_; 
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
v_newDecls_294_ = lean_ctor_get(v___x_282_, 11);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_313_ == 0)
{
v___x_296_ = v___x_282_;
v_isShared_297_ = v_isSharedCheck_313_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_newDecls_294_);
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
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_313_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v_toEnvExtension_299_; lean_object* v_asyncMode_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_298_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_299_ = lean_ctor_get(v___x_298_, 0);
v_asyncMode_300_ = lean_ctor_get(v_toEnvExtension_299_, 2);
v___x_301_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_a_276_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_box(0);
v___x_304_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_298_, v_env_283_, v___x_302_, v_asyncMode_300_, v___x_303_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_304_);
v___x_306_ = v___x_296_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_messages_284_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_312_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_312_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_312_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_312_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_312_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_312_, 10, v_snapshotTasks_293_);
lean_ctor_set(v_reuseFailAlloc_312_, 11, v_newDecls_294_);
v___x_306_ = v_reuseFailAlloc_312_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_st_ref_set(v___y_281_, v___x_306_);
v___x_308_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_308_);
v___x_310_ = v___x_278_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
v___jp_314_:
{
if (v___y_317_ == 0)
{
lean_dec(v___x_268_);
v___y_281_ = v___y_315_;
goto v___jp_280_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v___x_318_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_319_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_322_, v___y_316_, v___y_315_);
lean_dec(v___x_268_);
return v___x_323_;
}
}
v___jp_324_:
{
lean_object* v___x_327_; lean_object* v_env_328_; uint8_t v___x_329_; 
v___x_327_ = lean_st_ref_get(v___y_326_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
v___x_329_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_328_, v_a_276_);
if (v___x_329_ == 0)
{
v___y_315_ = v___y_326_;
v___y_316_ = v___y_325_;
v___y_317_ = v___x_270_;
goto v___jp_314_;
}
else
{
v___y_315_ = v___y_326_;
v___y_316_ = v___y_325_;
v___y_317_ = v___x_257_;
goto v___jp_314_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v_a_344_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_275_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_275_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v_cmd_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_256_);
v___x_352_ = lean_unsigned_to_nat(1u);
v_cmd_353_ = l_Lean_Syntax_getArg(v_x_247_, v___x_352_);
lean_dec(v_x_247_);
v___x_354_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_355_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_353_, v___x_354_, v_a_248_, v_a_249_);
lean_dec(v_cmd_353_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_361_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_377_, v_msg_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_383_, lean_object* v_ref_384_, lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_384_, v_msg_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_390_, lean_object* v_ref_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_390_, v_ref_391_, v_msg_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v_ref_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_397_, lean_object* v_macroStack_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_397_, v_macroStack_398_, v___y_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_403_, lean_object* v_macroStack_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_403_, v_macroStack_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_421_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_423_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_424_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_420_, v___x_421_, v___x_422_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_455_ = l_Lean_addBuiltinDeclarationRanges(v___x_453_, v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_457_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_val_473_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = l_Lean_Syntax_getArg(v_stx_462_, v___x_480_);
switch(lean_obj_tag(v___x_481_))
{
case 2:
{
lean_object* v_val_482_; 
lean_dec(v_stx_462_);
v_val_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc_ref(v_val_482_);
lean_dec_ref(v___x_481_);
v_val_473_ = v_val_482_;
goto v___jp_472_;
}
case 1:
{
lean_object* v_kind_483_; 
v_kind_483_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_kind_483_);
if (lean_obj_tag(v_kind_483_) == 1)
{
lean_object* v_pre_484_; 
v_pre_484_ = lean_ctor_get(v_kind_483_, 0);
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
lean_inc(v_pre_486_);
if (lean_obj_tag(v_pre_486_) == 1)
{
lean_object* v_pre_487_; 
v_pre_487_ = lean_ctor_get(v_pre_486_, 0);
if (lean_obj_tag(v_pre_487_) == 0)
{
lean_object* v_str_488_; lean_object* v_str_489_; lean_object* v_str_490_; lean_object* v_str_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_str_488_ = lean_ctor_get(v_kind_483_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref(v_kind_483_);
v_str_489_ = lean_ctor_get(v_pre_484_, 1);
lean_inc_ref(v_str_489_);
lean_dec_ref(v_pre_484_);
v_str_490_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref(v_pre_485_);
v_str_491_ = lean_ctor_get(v_pre_486_, 1);
lean_inc_ref(v_str_491_);
lean_dec_ref(v_pre_486_);
v___x_492_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_493_ = lean_string_dec_eq(v_str_491_, v___x_492_);
lean_dec_ref(v_str_491_);
if (v___x_493_ == 0)
{
lean_dec_ref(v_str_490_);
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_495_ = lean_string_dec_eq(v_str_490_, v___x_494_);
lean_dec_ref(v_str_490_);
if (v___x_495_ == 0)
{
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_497_ = lean_string_dec_eq(v_str_489_, v___x_496_);
lean_dec_ref(v_str_489_);
if (v___x_497_ == 0)
{
lean_dec_ref(v_str_488_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_499_ = lean_string_dec_eq(v_str_488_, v___x_498_);
lean_dec_ref(v_str_488_);
if (v___x_499_ == 0)
{
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = l_Lean_Syntax_getArg(v___x_481_, v___x_500_);
lean_dec_ref(v___x_481_);
if (lean_obj_tag(v___x_501_) == 2)
{
lean_object* v_val_502_; 
lean_dec(v_stx_462_);
v_val_502_ = lean_ctor_get(v___x_501_, 1);
lean_inc_ref(v_val_502_);
lean_dec_ref(v___x_501_);
v_val_473_ = v_val_502_;
goto v___jp_472_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___x_501_);
v___x_503_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_462_);
v___x_504_ = l_Lean_MessageData_ofSyntax(v_stx_462_);
v___x_505_ = l_Lean_indentD(v___x_504_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_503_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_462_, v___x_506_, v___y_463_, v___y_464_);
lean_dec(v_stx_462_);
return v___x_507_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_486_);
lean_dec_ref(v_pre_485_);
lean_dec_ref(v_pre_484_);
lean_dec_ref(v_kind_483_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
}
else
{
lean_dec(v_pre_486_);
lean_dec_ref(v_pre_485_);
lean_dec_ref(v_pre_484_);
lean_dec_ref(v_kind_483_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
}
else
{
lean_dec_ref(v_pre_484_);
lean_dec(v_pre_485_);
lean_dec_ref(v_kind_483_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
}
else
{
lean_dec_ref(v_kind_483_);
lean_dec(v_pre_484_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
}
else
{
lean_dec(v_kind_483_);
lean_dec_ref(v___x_481_);
goto v___jp_466_;
}
}
default: 
{
lean_dec(v___x_481_);
goto v___jp_466_;
}
}
v___jp_466_:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_467_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_462_);
v___x_468_ = l_Lean_MessageData_ofSyntax(v_stx_462_);
v___x_469_ = l_Lean_indentD(v___x_468_);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_467_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_462_, v___x_470_, v___y_463_, v___y_464_);
lean_dec(v_stx_462_);
return v___x_471_;
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_string_utf8_byte_size(v_val_473_);
v___x_476_ = lean_unsigned_to_nat(2u);
v___x_477_ = lean_nat_sub(v___x_475_, v___x_476_);
v___x_478_ = lean_string_utf8_extract(v_val_473_, v___x_474_, v___x_477_);
lean_dec(v___x_477_);
lean_dec_ref(v_val_473_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_512_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v_a_533_; lean_object* v_doc_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_525_);
v___x_602_ = l_Lean_Syntax_isOfKind(v_x_525_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_x_525_);
v___x_603_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_604_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_603_, v_a_526_, v_a_527_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Lean_Syntax_getArg(v_x_525_, v___x_605_);
v___x_607_ = l_Lean_Syntax_isNone(v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_606_);
v___x_609_ = l_Lean_Syntax_matchesNull(v___x_606_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v___x_606_);
lean_dec(v_x_525_);
v___x_610_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_611_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_610_, v_a_526_, v_a_527_);
return v___x_611_;
}
else
{
lean_object* v_doc_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_doc_612_ = l_Lean_Syntax_getArg(v___x_606_, v___x_605_);
lean_dec(v___x_606_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_doc_612_);
v___x_614_ = l_Lean_Syntax_isOfKind(v_doc_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_doc_612_);
lean_dec(v_x_525_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_616_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_615_, v_a_526_, v_a_527_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_doc_612_);
v_doc_567_ = v___x_617_;
v___y_568_ = v_a_526_;
v___y_569_ = v_a_527_;
goto v___jp_566_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec(v___x_606_);
v___x_618_ = lean_box(0);
v_doc_567_ = v___x_618_;
v___y_568_ = v_a_526_;
v___y_569_ = v_a_527_;
goto v___jp_566_;
}
}
v___jp_529_:
{
lean_object* v___x_534_; lean_object* v_env_535_; lean_object* v_messages_536_; lean_object* v_scopes_537_; lean_object* v_usedQuotCtxts_538_; lean_object* v_nextMacroScope_539_; lean_object* v_maxRecDepth_540_; lean_object* v_ngen_541_; lean_object* v_auxDeclNGen_542_; lean_object* v_infoState_543_; lean_object* v_traceState_544_; lean_object* v_snapshotTasks_545_; lean_object* v_newDecls_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_565_; 
v___x_534_ = lean_st_ref_take(v___y_532_);
v_env_535_ = lean_ctor_get(v___x_534_, 0);
v_messages_536_ = lean_ctor_get(v___x_534_, 1);
v_scopes_537_ = lean_ctor_get(v___x_534_, 2);
v_usedQuotCtxts_538_ = lean_ctor_get(v___x_534_, 3);
v_nextMacroScope_539_ = lean_ctor_get(v___x_534_, 4);
v_maxRecDepth_540_ = lean_ctor_get(v___x_534_, 5);
v_ngen_541_ = lean_ctor_get(v___x_534_, 6);
v_auxDeclNGen_542_ = lean_ctor_get(v___x_534_, 7);
v_infoState_543_ = lean_ctor_get(v___x_534_, 8);
v_traceState_544_ = lean_ctor_get(v___x_534_, 9);
v_snapshotTasks_545_ = lean_ctor_get(v___x_534_, 10);
v_newDecls_546_ = lean_ctor_get(v___x_534_, 11);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_565_ == 0)
{
v___x_548_ = v___x_534_;
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_newDecls_546_);
lean_inc(v_snapshotTasks_545_);
lean_inc(v_traceState_544_);
lean_inc(v_infoState_543_);
lean_inc(v_auxDeclNGen_542_);
lean_inc(v_ngen_541_);
lean_inc(v_maxRecDepth_540_);
lean_inc(v_nextMacroScope_539_);
lean_inc(v_usedQuotCtxts_538_);
lean_inc(v_scopes_537_);
lean_inc(v_messages_536_);
lean_inc(v_env_535_);
lean_dec(v___x_534_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_565_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v_toEnvExtension_551_; lean_object* v_asyncMode_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_550_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_551_ = lean_ctor_get(v___x_550_, 0);
v_asyncMode_552_ = lean_ctor_get(v_toEnvExtension_551_, 2);
v___x_553_ = l_Lean_TSyntax_getId(v___y_530_);
lean_dec(v___y_530_);
v___x_554_ = l_Lean_TSyntax_getString(v___y_531_);
lean_dec(v___y_531_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_a_533_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_553_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_box(0);
v___x_558_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_550_, v_env_535_, v___x_556_, v_asyncMode_552_, v___x_557_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_558_);
v___x_560_ = v___x_548_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_messages_536_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_scopes_537_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_usedQuotCtxts_538_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_nextMacroScope_539_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v_maxRecDepth_540_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v_ngen_541_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v_auxDeclNGen_542_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v_infoState_543_);
lean_ctor_set(v_reuseFailAlloc_564_, 9, v_traceState_544_);
lean_ctor_set(v_reuseFailAlloc_564_, 10, v_snapshotTasks_545_);
lean_ctor_set(v_reuseFailAlloc_564_, 11, v_newDecls_546_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_st_ref_set(v___y_532_, v___x_560_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
}
v___jp_566_:
{
lean_object* v___x_570_; lean_object* v_tag_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_570_ = lean_unsigned_to_nat(2u);
v_tag_571_ = l_Lean_Syntax_getArg(v_x_525_, v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v_tag_571_);
v___x_573_ = l_Lean_Syntax_isOfKind(v_tag_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_tag_571_);
lean_dec(v_doc_567_);
lean_dec(v_x_525_);
v___x_574_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_575_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_574_, v___y_568_, v___y_569_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v_user_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(3u);
v_user_577_ = l_Lean_Syntax_getArg(v_x_525_, v___x_576_);
lean_dec(v_x_525_);
v___x_578_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_577_);
v___x_579_ = l_Lean_Syntax_isOfKind(v_user_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v_user_577_);
lean_dec(v_tag_571_);
lean_dec(v_doc_567_);
v___x_580_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_581_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_580_, v___y_568_, v___y_569_);
return v___x_581_;
}
else
{
if (lean_obj_tag(v_doc_567_) == 0)
{
lean_object* v___x_582_; 
v___x_582_ = lean_box(0);
v___y_530_ = v_tag_571_;
v___y_531_ = v_user_577_;
v___y_532_ = v___y_569_;
v_a_533_ = v___x_582_;
goto v___jp_529_;
}
else
{
lean_object* v_val_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_600_; 
v_val_583_ = lean_ctor_get(v_doc_567_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_doc_567_);
if (v_isSharedCheck_600_ == 0)
{
v___x_585_ = v_doc_567_;
v_isShared_586_ = v_isSharedCheck_600_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_val_583_);
lean_dec(v_doc_567_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_600_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_583_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_587_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v_a_588_);
v___x_590_ = v___x_585_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
v___y_530_ = v_tag_571_;
v___y_531_ = v_user_577_;
v___y_532_ = v___y_569_;
v_a_533_ = v___x_590_;
goto v___jp_529_;
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_del_object(v___x_585_);
lean_dec(v_user_577_);
lean_dec(v_tag_571_);
v_a_592_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_587_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_633_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_635_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_636_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_632_, v___x_633_, v___x_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_667_ = l_Lean_addBuiltinDeclarationRanges(v___x_665_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
return v___x_672_;
}
else
{
lean_dec_ref(v___x_670_);
lean_inc_ref(v_x_671_);
return v_x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_673_, v_x_674_);
lean_dec(v_x_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_676_, lean_object* v_k_677_, lean_object* v_t_678_){
_start:
{
if (lean_obj_tag(v_t_678_) == 0)
{
lean_object* v_size_679_; lean_object* v_k_680_; lean_object* v_v_681_; lean_object* v_l_682_; lean_object* v_r_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_1009_; 
v_size_679_ = lean_ctor_get(v_t_678_, 0);
v_k_680_ = lean_ctor_get(v_t_678_, 1);
v_v_681_ = lean_ctor_get(v_t_678_, 2);
v_l_682_ = lean_ctor_get(v_t_678_, 3);
v_r_683_ = lean_ctor_get(v_t_678_, 4);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_t_678_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_685_ = v_t_678_;
v_isShared_686_ = v_isSharedCheck_1009_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_r_683_);
lean_inc(v_l_682_);
lean_inc(v_v_681_);
lean_inc(v_k_680_);
lean_inc(v_size_679_);
lean_dec(v_t_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_1009_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint8_t v___x_687_; 
v___x_687_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_677_, v_k_680_);
switch(v___x_687_)
{
case 0:
{
lean_object* v_impl_688_; lean_object* v___x_689_; 
lean_del_object(v___x_685_);
lean_dec(v_size_679_);
v_impl_688_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_676_, v_k_677_, v_l_682_);
v___x_689_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_680_, v_v_681_, v_impl_688_, v_r_683_);
return v___x_689_;
}
case 1:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v_k_680_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v_v_681_);
v___x_691_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_676_, v___x_690_);
lean_dec_ref(v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_del_object(v___x_685_);
lean_dec(v_size_679_);
lean_dec(v_k_677_);
if (lean_obj_tag(v_l_682_) == 0)
{
if (lean_obj_tag(v_r_683_) == 0)
{
lean_object* v_size_692_; lean_object* v_k_693_; lean_object* v_v_694_; lean_object* v_l_695_; lean_object* v_r_696_; lean_object* v_size_697_; lean_object* v_k_698_; lean_object* v_v_699_; lean_object* v_l_700_; lean_object* v_r_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_size_692_ = lean_ctor_get(v_l_682_, 0);
v_k_693_ = lean_ctor_get(v_l_682_, 1);
v_v_694_ = lean_ctor_get(v_l_682_, 2);
v_l_695_ = lean_ctor_get(v_l_682_, 3);
v_r_696_ = lean_ctor_get(v_l_682_, 4);
lean_inc(v_r_696_);
v_size_697_ = lean_ctor_get(v_r_683_, 0);
v_k_698_ = lean_ctor_get(v_r_683_, 1);
v_v_699_ = lean_ctor_get(v_r_683_, 2);
v_l_700_ = lean_ctor_get(v_r_683_, 3);
lean_inc(v_l_700_);
v_r_701_ = lean_ctor_get(v_r_683_, 4);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_dec_lt(v_size_692_, v_size_697_);
if (v___x_703_ == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_839_; 
lean_inc(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
v_isSharedCheck_839_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_840_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_844_);
v___x_705_ = v_l_682_;
v_isShared_706_ = v_isSharedCheck_839_;
goto v_resetjp_704_;
}
else
{
lean_dec(v_l_682_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_839_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v_tree_708_; 
v___x_707_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_693_, v_v_694_, v_l_695_, v_r_696_);
v_tree_708_ = lean_ctor_get(v___x_707_, 2);
lean_inc(v_tree_708_);
if (lean_obj_tag(v_tree_708_) == 0)
{
lean_object* v_k_709_; lean_object* v_v_710_; lean_object* v_size_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_k_709_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_709_);
v_v_710_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_710_);
lean_dec_ref(v___x_707_);
v_size_711_ = lean_ctor_get(v_tree_708_, 0);
v___x_712_ = lean_unsigned_to_nat(3u);
v___x_713_ = lean_nat_mul(v___x_712_, v_size_711_);
v___x_714_ = lean_nat_dec_lt(v___x_713_, v_size_697_);
lean_dec(v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
lean_dec(v_l_700_);
v___x_715_ = lean_nat_add(v___x_702_, v_size_711_);
v___x_716_ = lean_nat_add(v___x_715_, v_size_697_);
lean_dec(v___x_715_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_683_);
lean_ctor_set(v___x_705_, 3, v_tree_708_);
lean_ctor_set(v___x_705_, 2, v_v_710_);
lean_ctor_set(v___x_705_, 1, v_k_709_);
lean_ctor_set(v___x_705_, 0, v___x_716_);
v___x_718_ = v___x_705_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_r_683_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_774_; 
lean_inc(v_r_701_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_774_ = !lean_is_exclusive(v_r_683_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_775_ = lean_ctor_get(v_r_683_, 4);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_683_, 3);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_r_683_, 2);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_r_683_, 1);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_r_683_, 0);
lean_dec(v_unused_779_);
v___x_721_ = v_r_683_;
v_isShared_722_ = v_isSharedCheck_774_;
goto v_resetjp_720_;
}
else
{
lean_dec(v_r_683_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_774_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_size_723_; lean_object* v_k_724_; lean_object* v_v_725_; lean_object* v_l_726_; lean_object* v_r_727_; lean_object* v_size_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_size_723_ = lean_ctor_get(v_l_700_, 0);
v_k_724_ = lean_ctor_get(v_l_700_, 1);
v_v_725_ = lean_ctor_get(v_l_700_, 2);
v_l_726_ = lean_ctor_get(v_l_700_, 3);
v_r_727_ = lean_ctor_get(v_l_700_, 4);
v_size_728_ = lean_ctor_get(v_r_701_, 0);
v___x_729_ = lean_unsigned_to_nat(2u);
v___x_730_ = lean_nat_mul(v___x_729_, v_size_728_);
v___x_731_ = lean_nat_dec_lt(v_size_723_, v___x_730_);
lean_dec(v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_759_; 
lean_inc(v_r_727_);
lean_inc(v_l_726_);
lean_inc(v_v_725_);
lean_inc(v_k_724_);
v_isSharedCheck_759_ = !lean_is_exclusive(v_l_700_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_760_ = lean_ctor_get(v_l_700_, 4);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_l_700_, 3);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_l_700_, 2);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_l_700_, 1);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_l_700_, 0);
lean_dec(v_unused_764_);
v___x_733_ = v_l_700_;
v_isShared_734_ = v_isSharedCheck_759_;
goto v_resetjp_732_;
}
else
{
lean_dec(v_l_700_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_759_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_749_; 
v___x_735_ = lean_nat_add(v___x_702_, v_size_711_);
v___x_736_ = lean_nat_add(v___x_735_, v_size_697_);
lean_dec(v_size_697_);
if (lean_obj_tag(v_l_726_) == 0)
{
lean_object* v_size_757_; 
v_size_757_ = lean_ctor_get(v_l_726_, 0);
lean_inc(v_size_757_);
v___y_749_ = v_size_757_;
goto v___jp_748_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___y_749_ = v___x_758_;
goto v___jp_748_;
}
v___jp_737_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_nat_add(v___y_738_, v___y_740_);
lean_dec(v___y_740_);
lean_dec(v___y_738_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 4, v_r_701_);
lean_ctor_set(v___x_733_, 3, v_r_727_);
lean_ctor_set(v___x_733_, 2, v_v_699_);
lean_ctor_set(v___x_733_, 1, v_k_698_);
lean_ctor_set(v___x_733_, 0, v___x_741_);
v___x_743_ = v___x_733_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_r_727_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_r_701_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 4, v___x_743_);
lean_ctor_set(v___x_721_, 3, v___y_739_);
lean_ctor_set(v___x_721_, 2, v_v_725_);
lean_ctor_set(v___x_721_, 1, v_k_724_);
lean_ctor_set(v___x_721_, 0, v___x_736_);
v___x_745_ = v___x_721_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_724_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_725_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v___y_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_nat_add(v___x_735_, v___y_749_);
lean_dec(v___y_749_);
lean_dec(v___x_735_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_l_726_);
lean_ctor_set(v___x_705_, 3, v_tree_708_);
lean_ctor_set(v___x_705_, 2, v_v_710_);
lean_ctor_set(v___x_705_, 1, v_k_709_);
lean_ctor_set(v___x_705_, 0, v___x_750_);
v___x_752_ = v___x_705_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_l_726_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_nat_add(v___x_702_, v_size_728_);
if (lean_obj_tag(v_r_727_) == 0)
{
lean_object* v_size_754_; 
v_size_754_ = lean_ctor_get(v_r_727_, 0);
lean_inc(v_size_754_);
v___y_738_ = v___x_753_;
v___y_739_ = v___x_752_;
v___y_740_ = v_size_754_;
goto v___jp_737_;
}
else
{
lean_object* v___x_755_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___y_738_ = v___x_753_;
v___y_739_ = v___x_752_;
v___y_740_ = v___x_755_;
goto v___jp_737_;
}
}
}
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_765_ = lean_nat_add(v___x_702_, v_size_711_);
v___x_766_ = lean_nat_add(v___x_765_, v_size_697_);
lean_dec(v_size_697_);
v___x_767_ = lean_nat_add(v___x_765_, v_size_723_);
lean_dec(v___x_765_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 4, v_l_700_);
lean_ctor_set(v___x_721_, 3, v_tree_708_);
lean_ctor_set(v___x_721_, 2, v_v_710_);
lean_ctor_set(v___x_721_, 1, v_k_709_);
lean_ctor_set(v___x_721_, 0, v___x_767_);
v___x_769_ = v___x_721_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_l_700_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_701_);
lean_ctor_set(v___x_705_, 3, v___x_769_);
lean_ctor_set(v___x_705_, 2, v_v_699_);
lean_ctor_set(v___x_705_, 1, v_k_698_);
lean_ctor_set(v___x_705_, 0, v___x_766_);
v___x_771_ = v___x_705_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_r_701_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
else
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_833_; 
lean_inc(v_r_701_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_833_ = !lean_is_exclusive(v_r_683_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_834_ = lean_ctor_get(v_r_683_, 4);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_683_, 3);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_r_683_, 2);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_r_683_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_r_683_, 0);
lean_dec(v_unused_838_);
v___x_781_ = v_r_683_;
v_isShared_782_ = v_isSharedCheck_833_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_r_683_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_833_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
if (lean_obj_tag(v_l_700_) == 0)
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v_k_783_; lean_object* v_v_784_; lean_object* v_size_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v_k_783_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_783_);
v_v_784_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_784_);
lean_dec_ref(v___x_707_);
v_size_785_ = lean_ctor_get(v_l_700_, 0);
v___x_786_ = lean_nat_add(v___x_702_, v_size_697_);
lean_dec(v_size_697_);
v___x_787_ = lean_nat_add(v___x_702_, v_size_785_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 4, v_l_700_);
lean_ctor_set(v___x_781_, 3, v_tree_708_);
lean_ctor_set(v___x_781_, 2, v_v_784_);
lean_ctor_set(v___x_781_, 1, v_k_783_);
lean_ctor_set(v___x_781_, 0, v___x_787_);
v___x_789_ = v___x_781_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_k_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v_v_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_tree_708_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_l_700_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_701_);
lean_ctor_set(v___x_705_, 3, v___x_789_);
lean_ctor_set(v___x_705_, 2, v_v_699_);
lean_ctor_set(v___x_705_, 1, v_k_698_);
lean_ctor_set(v___x_705_, 0, v___x_786_);
v___x_791_ = v___x_705_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_792_, 3, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 4, v_r_701_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v_k_796_; lean_object* v_v_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_size_697_);
v_k_794_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_794_);
v_v_795_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_795_);
lean_dec_ref(v___x_707_);
v_k_796_ = lean_ctor_get(v_l_700_, 1);
v_v_797_ = lean_ctor_get(v_l_700_, 2);
v_isSharedCheck_811_ = !lean_is_exclusive(v_l_700_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; lean_object* v_unused_813_; lean_object* v_unused_814_; 
v_unused_812_ = lean_ctor_get(v_l_700_, 4);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_l_700_, 3);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_l_700_, 0);
lean_dec(v_unused_814_);
v___x_799_ = v_l_700_;
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_v_797_);
lean_inc(v_k_796_);
lean_dec(v_l_700_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_811_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_unsigned_to_nat(3u);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v_r_701_);
lean_ctor_set(v___x_799_, 3, v_r_701_);
lean_ctor_set(v___x_799_, 2, v_v_795_);
lean_ctor_set(v___x_799_, 1, v_k_794_);
lean_ctor_set(v___x_799_, 0, v___x_702_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_810_, 4, v_r_701_);
v___x_803_ = v_reuseFailAlloc_810_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 3, v_r_701_);
lean_ctor_set(v___x_781_, 0, v___x_702_);
v___x_805_ = v___x_781_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_809_, 4, v_r_701_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v___x_805_);
lean_ctor_set(v___x_705_, 3, v___x_803_);
lean_ctor_set(v___x_705_, 2, v_v_797_);
lean_ctor_set(v___x_705_, 1, v_k_796_);
lean_ctor_set(v___x_705_, 0, v___x_801_);
v___x_807_ = v___x_705_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v___x_805_);
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
}
}
else
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v_k_815_; lean_object* v_v_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec(v_size_697_);
v_k_815_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_815_);
v_v_816_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_816_);
lean_dec_ref(v___x_707_);
v___x_817_ = lean_unsigned_to_nat(3u);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 4, v_l_700_);
lean_ctor_set(v___x_781_, 2, v_v_816_);
lean_ctor_set(v___x_781_, 1, v_k_815_);
lean_ctor_set(v___x_781_, 0, v___x_702_);
v___x_819_ = v___x_781_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_k_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_v_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_l_700_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v_r_701_);
lean_ctor_set(v___x_705_, 3, v___x_819_);
lean_ctor_set(v___x_705_, 2, v_v_699_);
lean_ctor_set(v___x_705_, 1, v_k_698_);
lean_ctor_set(v___x_705_, 0, v___x_817_);
v___x_821_ = v___x_705_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 4, v_r_701_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
else
{
lean_object* v_k_824_; lean_object* v_v_825_; lean_object* v___x_827_; 
v_k_824_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_k_824_);
v_v_825_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_v_825_);
lean_dec_ref(v___x_707_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 3, v_r_701_);
v___x_827_ = v___x_781_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_size_697_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_r_701_);
v___x_827_ = v_reuseFailAlloc_832_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(2u);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 4, v___x_827_);
lean_ctor_set(v___x_705_, 3, v_r_701_);
lean_ctor_set(v___x_705_, 2, v_v_825_);
lean_ctor_set(v___x_705_, 1, v_k_824_);
lean_ctor_set(v___x_705_, 0, v___x_828_);
v___x_830_ = v___x_705_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_k_824_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_v_825_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v___x_827_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
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
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_997_; 
lean_inc(v_r_701_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
v_isSharedCheck_997_ = !lean_is_exclusive(v_r_683_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; lean_object* v_unused_1001_; lean_object* v_unused_1002_; 
v_unused_998_ = lean_ctor_get(v_r_683_, 4);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_683_, 3);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_r_683_, 2);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_r_683_, 1);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_r_683_, 0);
lean_dec(v_unused_1002_);
v___x_846_ = v_r_683_;
v_isShared_847_ = v_isSharedCheck_997_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_r_683_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_997_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v_tree_849_; 
v___x_848_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_698_, v_v_699_, v_l_700_, v_r_701_);
v_tree_849_ = lean_ctor_get(v___x_848_, 2);
lean_inc(v_tree_849_);
if (lean_obj_tag(v_tree_849_) == 0)
{
lean_object* v_k_850_; lean_object* v_v_851_; lean_object* v_size_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_k_850_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_850_);
v_v_851_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_851_);
lean_dec_ref(v___x_848_);
v_size_852_ = lean_ctor_get(v_tree_849_, 0);
v___x_853_ = lean_unsigned_to_nat(3u);
v___x_854_ = lean_nat_mul(v___x_853_, v_size_852_);
v___x_855_ = lean_nat_dec_lt(v___x_854_, v_size_692_);
lean_dec(v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec(v_r_696_);
v___x_856_ = lean_nat_add(v___x_702_, v_size_692_);
v___x_857_ = lean_nat_add(v___x_856_, v_size_852_);
lean_dec(v___x_856_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_tree_849_);
lean_ctor_set(v___x_846_, 3, v_l_682_);
lean_ctor_set(v___x_846_, 2, v_v_851_);
lean_ctor_set(v___x_846_, 1, v_k_850_);
lean_ctor_set(v___x_846_, 0, v___x_857_);
v___x_859_ = v___x_846_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_k_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_v_851_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_860_, 4, v_tree_849_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_926_; 
lean_inc(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
lean_inc(v_size_692_);
v_isSharedCheck_926_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; lean_object* v_unused_930_; lean_object* v_unused_931_; 
v_unused_927_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_931_);
v___x_862_ = v_l_682_;
v_isShared_863_ = v_isSharedCheck_926_;
goto v_resetjp_861_;
}
else
{
lean_dec(v_l_682_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_926_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_size_864_; lean_object* v_size_865_; lean_object* v_k_866_; lean_object* v_v_867_; lean_object* v_l_868_; lean_object* v_r_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_size_864_ = lean_ctor_get(v_l_695_, 0);
v_size_865_ = lean_ctor_get(v_r_696_, 0);
v_k_866_ = lean_ctor_get(v_r_696_, 1);
v_v_867_ = lean_ctor_get(v_r_696_, 2);
v_l_868_ = lean_ctor_get(v_r_696_, 3);
v_r_869_ = lean_ctor_get(v_r_696_, 4);
v___x_870_ = lean_unsigned_to_nat(2u);
v___x_871_ = lean_nat_mul(v___x_870_, v_size_864_);
v___x_872_ = lean_nat_dec_lt(v_size_865_, v___x_871_);
lean_dec(v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_910_; 
lean_inc(v_r_869_);
lean_inc(v_l_868_);
lean_inc(v_v_867_);
lean_inc(v_k_866_);
lean_del_object(v___x_862_);
v_isSharedCheck_910_ = !lean_is_exclusive(v_r_696_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; lean_object* v_unused_914_; lean_object* v_unused_915_; 
v_unused_911_ = lean_ctor_get(v_r_696_, 4);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_r_696_, 3);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_r_696_, 2);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_r_696_, 1);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_r_696_, 0);
lean_dec(v_unused_915_);
v___x_874_ = v_r_696_;
v_isShared_875_ = v_isSharedCheck_910_;
goto v_resetjp_873_;
}
else
{
lean_dec(v_r_696_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_910_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___x_898_; lean_object* v___y_900_; 
v___x_876_ = lean_nat_add(v___x_702_, v_size_692_);
lean_dec(v_size_692_);
v___x_877_ = lean_nat_add(v___x_876_, v_size_852_);
lean_dec(v___x_876_);
v___x_898_ = lean_nat_add(v___x_702_, v_size_864_);
if (lean_obj_tag(v_l_868_) == 0)
{
lean_object* v_size_908_; 
v_size_908_ = lean_ctor_get(v_l_868_, 0);
lean_inc(v_size_908_);
v___y_900_ = v_size_908_;
goto v___jp_899_;
}
else
{
lean_object* v___x_909_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___y_900_ = v___x_909_;
goto v___jp_899_;
}
v___jp_878_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_nat_add(v___y_879_, v___y_881_);
lean_dec(v___y_881_);
lean_dec(v___y_879_);
lean_inc_ref(v_tree_849_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 4, v_tree_849_);
lean_ctor_set(v___x_874_, 3, v_r_869_);
lean_ctor_set(v___x_874_, 2, v_v_851_);
lean_ctor_set(v___x_874_, 1, v_k_850_);
lean_ctor_set(v___x_874_, 0, v___x_882_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_k_850_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_v_851_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_r_869_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_tree_849_);
v___x_884_ = v_reuseFailAlloc_897_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
v_isSharedCheck_891_ = !lean_is_exclusive(v_tree_849_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; lean_object* v_unused_895_; lean_object* v_unused_896_; 
v_unused_892_ = lean_ctor_get(v_tree_849_, 4);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_tree_849_, 3);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_tree_849_, 2);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_tree_849_, 1);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_tree_849_, 0);
lean_dec(v_unused_896_);
v___x_886_ = v_tree_849_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_dec(v_tree_849_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 4, v___x_884_);
lean_ctor_set(v___x_886_, 3, v___y_880_);
lean_ctor_set(v___x_886_, 2, v_v_867_);
lean_ctor_set(v___x_886_, 1, v_k_866_);
lean_ctor_set(v___x_886_, 0, v___x_877_);
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_k_866_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_v_867_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v___y_880_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v___x_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
v___jp_899_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_nat_add(v___x_898_, v___y_900_);
lean_dec(v___y_900_);
lean_dec(v___x_898_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_l_868_);
lean_ctor_set(v___x_846_, 3, v_l_695_);
lean_ctor_set(v___x_846_, 2, v_v_694_);
lean_ctor_set(v___x_846_, 1, v_k_693_);
lean_ctor_set(v___x_846_, 0, v___x_901_);
v___x_903_ = v___x_846_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_l_868_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = lean_nat_add(v___x_702_, v_size_852_);
if (lean_obj_tag(v_r_869_) == 0)
{
lean_object* v_size_905_; 
v_size_905_ = lean_ctor_get(v_r_869_, 0);
lean_inc(v_size_905_);
v___y_879_ = v___x_904_;
v___y_880_ = v___x_903_;
v___y_881_ = v_size_905_;
goto v___jp_878_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_unsigned_to_nat(0u);
v___y_879_ = v___x_904_;
v___y_880_ = v___x_903_;
v___y_881_ = v___x_906_;
goto v___jp_878_;
}
}
}
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_916_ = lean_nat_add(v___x_702_, v_size_692_);
lean_dec(v_size_692_);
v___x_917_ = lean_nat_add(v___x_916_, v_size_852_);
lean_dec(v___x_916_);
v___x_918_ = lean_nat_add(v___x_702_, v_size_852_);
v___x_919_ = lean_nat_add(v___x_918_, v_size_865_);
lean_dec(v___x_918_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_tree_849_);
lean_ctor_set(v___x_846_, 3, v_r_696_);
lean_ctor_set(v___x_846_, 2, v_v_851_);
lean_ctor_set(v___x_846_, 1, v_k_850_);
lean_ctor_set(v___x_846_, 0, v___x_919_);
v___x_921_ = v___x_846_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_k_850_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_v_851_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_r_696_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_tree_849_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 4, v___x_921_);
lean_ctor_set(v___x_862_, 0, v___x_917_);
v___x_923_ = v___x_862_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_695_) == 0)
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_955_; 
lean_inc_ref(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
lean_inc(v_size_692_);
v_isSharedCheck_955_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; lean_object* v_unused_959_; lean_object* v_unused_960_; 
v_unused_956_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_960_);
v___x_933_ = v_l_682_;
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
else
{
lean_dec(v_l_682_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_955_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
if (lean_obj_tag(v_r_696_) == 0)
{
lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v_size_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v_k_935_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_935_);
v_v_936_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_936_);
lean_dec_ref(v___x_848_);
v_size_937_ = lean_ctor_get(v_r_696_, 0);
v___x_938_ = lean_nat_add(v___x_702_, v_size_692_);
lean_dec(v_size_692_);
v___x_939_ = lean_nat_add(v___x_702_, v_size_937_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_tree_849_);
lean_ctor_set(v___x_846_, 3, v_r_696_);
lean_ctor_set(v___x_846_, 2, v_v_936_);
lean_ctor_set(v___x_846_, 1, v_k_935_);
lean_ctor_set(v___x_846_, 0, v___x_939_);
v___x_941_ = v___x_846_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_936_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_r_696_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_tree_849_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_943_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v___x_941_);
lean_ctor_set(v___x_933_, 0, v___x_938_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v_k_946_; lean_object* v_v_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_size_692_);
v_k_946_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_946_);
v_v_947_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_947_);
lean_dec_ref(v___x_848_);
v___x_948_ = lean_unsigned_to_nat(3u);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_r_696_);
lean_ctor_set(v___x_846_, 3, v_r_696_);
lean_ctor_set(v___x_846_, 2, v_v_947_);
lean_ctor_set(v___x_846_, 1, v_k_946_);
lean_ctor_set(v___x_846_, 0, v___x_702_);
v___x_950_ = v___x_846_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_k_946_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_v_947_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_r_696_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_r_696_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_952_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v___x_950_);
lean_ctor_set(v___x_933_, 0, v___x_948_);
v___x_952_ = v___x_933_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_696_) == 0)
{
lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_985_; 
lean_inc(v_l_695_);
lean_inc(v_v_694_);
lean_inc(v_k_693_);
v_isSharedCheck_985_ = !lean_is_exclusive(v_l_682_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_l_682_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_682_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_682_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_l_682_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_l_682_, 0);
lean_dec(v_unused_990_);
v___x_962_ = v_l_682_;
v_isShared_963_ = v_isSharedCheck_985_;
goto v_resetjp_961_;
}
else
{
lean_dec(v_l_682_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_985_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_k_964_; lean_object* v_v_965_; lean_object* v_k_966_; lean_object* v_v_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_981_; 
v_k_964_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_964_);
v_v_965_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_965_);
lean_dec_ref(v___x_848_);
v_k_966_ = lean_ctor_get(v_r_696_, 1);
v_v_967_ = lean_ctor_get(v_r_696_, 2);
v_isSharedCheck_981_ = !lean_is_exclusive(v_r_696_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; lean_object* v_unused_983_; lean_object* v_unused_984_; 
v_unused_982_ = lean_ctor_get(v_r_696_, 4);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_r_696_, 3);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_r_696_, 0);
lean_dec(v_unused_984_);
v___x_969_ = v_r_696_;
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_v_967_);
lean_inc(v_k_966_);
lean_dec(v_r_696_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_981_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_unsigned_to_nat(3u);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 4, v_l_695_);
lean_ctor_set(v___x_969_, 3, v_l_695_);
lean_ctor_set(v___x_969_, 2, v_v_694_);
lean_ctor_set(v___x_969_, 1, v_k_693_);
lean_ctor_set(v___x_969_, 0, v___x_702_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_k_693_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v_v_694_);
lean_ctor_set(v_reuseFailAlloc_980_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_980_, 4, v_l_695_);
v___x_973_ = v_reuseFailAlloc_980_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_l_695_);
lean_ctor_set(v___x_846_, 3, v_l_695_);
lean_ctor_set(v___x_846_, 2, v_v_965_);
lean_ctor_set(v___x_846_, 1, v_k_964_);
lean_ctor_set(v___x_846_, 0, v___x_702_);
v___x_975_ = v___x_846_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_k_964_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_v_965_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_l_695_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_l_695_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 4, v___x_975_);
lean_ctor_set(v___x_962_, 3, v___x_973_);
lean_ctor_set(v___x_962_, 2, v_v_967_);
lean_ctor_set(v___x_962_, 1, v_k_966_);
lean_ctor_set(v___x_962_, 0, v___x_971_);
v___x_977_ = v___x_962_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_966_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_967_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
else
{
lean_object* v_k_991_; lean_object* v_v_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v_k_991_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_k_991_);
v_v_992_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_v_992_);
lean_dec_ref(v___x_848_);
v___x_993_ = lean_unsigned_to_nat(2u);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 4, v_r_696_);
lean_ctor_set(v___x_846_, 3, v_l_682_);
lean_ctor_set(v___x_846_, 2, v_v_992_);
lean_ctor_set(v___x_846_, 1, v_k_991_);
lean_ctor_set(v___x_846_, 0, v___x_993_);
v___x_995_ = v___x_846_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_k_991_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_v_992_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_r_696_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
else
{
return v_l_682_;
}
}
else
{
return v_r_683_;
}
}
else
{
lean_object* v_val_1003_; lean_object* v___x_1005_; 
v_val_1003_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_val_1003_);
lean_dec_ref(v___x_691_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 2, v_val_1003_);
lean_ctor_set(v___x_685_, 1, v_k_677_);
v___x_1005_ = v___x_685_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_size_679_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_677_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_val_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_l_682_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_r_683_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
default: 
{
lean_object* v_impl_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_685_);
lean_dec(v_size_679_);
v_impl_1007_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_676_, v_k_677_, v_r_683_);
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_680_, v_v_681_, v_l_682_, v_impl_1007_);
return v___x_1008_;
}
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_676_, v___x_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_dec(v_k_677_);
return v_t_678_;
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_val_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_val_1012_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = lean_unsigned_to_nat(1u);
v___x_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_k_677_);
lean_ctor_set(v___x_1014_, 2, v_val_1012_);
lean_ctor_set(v___x_1014_, 3, v_t_678_);
lean_ctor_set(v___x_1014_, 4, v_t_678_);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1015_, lean_object* v_i_1016_, lean_object* v_k_1017_){
_start:
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_array_get_size(v_keys_1015_);
v___x_1019_ = lean_nat_dec_lt(v_i_1016_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec(v_i_1016_);
return v___x_1019_;
}
else
{
lean_object* v_k_x27_1020_; uint8_t v___x_1021_; 
v_k_x27_1020_ = lean_array_fget_borrowed(v_keys_1015_, v_i_1016_);
v___x_1021_ = lean_name_eq(v_k_1017_, v_k_x27_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_i_1016_, v___x_1022_);
lean_dec(v_i_1016_);
v_i_1016_ = v___x_1023_;
goto _start;
}
else
{
lean_dec(v_i_1016_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1025_, lean_object* v_i_1026_, lean_object* v_k_1027_){
_start:
{
uint8_t v_res_1028_; lean_object* v_r_1029_; 
v_res_1028_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1025_, v_i_1026_, v_k_1027_);
lean_dec(v_k_1027_);
lean_dec_ref(v_keys_1025_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; 
v___x_1030_ = ((size_t)5ULL);
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_shift_left(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; 
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0);
v___x_1035_ = lean_usize_sub(v___x_1034_, v___x_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1036_, size_t v_x_1037_, lean_object* v_x_1038_){
_start:
{
if (lean_obj_tag(v_x_1036_) == 0)
{
lean_object* v_es_1039_; lean_object* v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; lean_object* v_j_1044_; lean_object* v___x_1045_; 
v_es_1039_ = lean_ctor_get(v_x_1036_, 0);
v___x_1040_ = lean_box(2);
v___x_1041_ = ((size_t)5ULL);
v___x_1042_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1043_ = lean_usize_land(v_x_1037_, v___x_1042_);
v_j_1044_ = lean_usize_to_nat(v___x_1043_);
v___x_1045_ = lean_array_get_borrowed(v___x_1040_, v_es_1039_, v_j_1044_);
lean_dec(v_j_1044_);
switch(lean_obj_tag(v___x_1045_))
{
case 0:
{
lean_object* v_key_1046_; uint8_t v___x_1047_; 
v_key_1046_ = lean_ctor_get(v___x_1045_, 0);
v___x_1047_ = lean_name_eq(v_x_1038_, v_key_1046_);
return v___x_1047_;
}
case 1:
{
lean_object* v_node_1048_; size_t v___x_1049_; 
v_node_1048_ = lean_ctor_get(v___x_1045_, 0);
v___x_1049_ = lean_usize_shift_right(v_x_1037_, v___x_1041_);
v_x_1036_ = v_node_1048_;
v_x_1037_ = v___x_1049_;
goto _start;
}
default: 
{
uint8_t v___x_1051_; 
v___x_1051_ = 0;
return v___x_1051_;
}
}
}
else
{
lean_object* v_ks_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_ks_1052_ = lean_ctor_get(v_x_1036_, 0);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1052_, v___x_1053_, v_x_1038_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_){
_start:
{
size_t v_x_4174__boxed_1058_; uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_x_4174__boxed_1058_ = lean_unbox_usize(v_x_1056_);
lean_dec(v_x_1056_);
v_res_1059_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1055_, v_x_4174__boxed_1058_, v_x_1057_);
lean_dec(v_x_1057_);
lean_dec_ref(v_x_1055_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1061_; uint64_t v___x_1062_; 
v___x_1061_ = lean_unsigned_to_nat(1723u);
v___x_1062_ = lean_uint64_of_nat(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
uint64_t v___y_1066_; 
if (lean_obj_tag(v_x_1064_) == 0)
{
uint64_t v___x_1069_; 
v___x_1069_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1066_ = v___x_1069_;
goto v___jp_1065_;
}
else
{
uint64_t v_hash_1070_; 
v_hash_1070_ = lean_ctor_get_uint64(v_x_1064_, sizeof(void*)*2);
v___y_1066_ = v_hash_1070_;
goto v___jp_1065_;
}
v___jp_1065_:
{
size_t v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_uint64_to_usize(v___y_1066_);
v___x_1068_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1063_, v___x_1067_, v_x_1064_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1071_, v_x_1072_);
lean_dec(v_x_1072_);
lean_dec_ref(v_x_1071_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1075_, lean_object* v_a_1076_, uint8_t v___x_1077_, lean_object* v_x_1078_, lean_object* v_____s_1079_){
_start:
{
lean_object* v_fst_1080_; lean_object* v_kinds_1081_; uint8_t v___x_1082_; 
v_fst_1080_ = lean_ctor_get(v_x_1078_, 0);
lean_inc(v_fst_1080_);
lean_dec_ref(v_x_1078_);
v_kinds_1081_ = lean_ctor_get(v_tactics_1075_, 1);
v___x_1082_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1081_, v_fst_1080_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; 
lean_dec(v_fst_1080_);
lean_dec(v_a_1076_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_____s_1079_);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = l_Lean_Name_toString(v_a_1076_, v___x_1077_);
v___x_1085_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1084_, v_fst_1080_, v_____s_1079_);
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1087_, lean_object* v_a_1088_, lean_object* v___x_1089_, lean_object* v_x_1090_, lean_object* v_____s_1091_){
_start:
{
uint8_t v___x_4242__boxed_1092_; lean_object* v_res_1093_; 
v___x_4242__boxed_1092_ = lean_unbox(v___x_1089_);
v_res_1093_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1087_, v_a_1088_, v___x_4242__boxed_1092_, v_x_1090_, v_____s_1091_);
lean_dec_ref(v_tactics_1087_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1094_, lean_object* v_keys_1095_, lean_object* v_vals_1096_, lean_object* v_i_1097_, lean_object* v_acc_1098_){
_start:
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = lean_array_get_size(v_keys_1095_);
v___x_1100_ = lean_nat_dec_lt(v_i_1097_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec(v_i_1097_);
lean_dec_ref(v_f_1094_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_acc_1098_);
return v___x_1101_;
}
else
{
lean_object* v_k_1102_; lean_object* v_v_1103_; lean_object* v___x_1104_; 
v_k_1102_ = lean_array_fget_borrowed(v_keys_1095_, v_i_1097_);
v_v_1103_ = lean_array_fget_borrowed(v_vals_1096_, v_i_1097_);
lean_inc_ref(v_f_1094_);
lean_inc(v_v_1103_);
lean_inc(v_k_1102_);
v___x_1104_ = lean_apply_3(v_f_1094_, v_acc_1098_, v_k_1102_, v_v_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_dec(v_i_1097_);
lean_dec_ref(v_f_1094_);
return v___x_1104_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___x_1104_);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_add(v_i_1097_, v___x_1106_);
lean_dec(v_i_1097_);
v_i_1097_ = v___x_1107_;
v_acc_1098_ = v_a_1105_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1109_, lean_object* v_keys_1110_, lean_object* v_vals_1111_, lean_object* v_i_1112_, lean_object* v_acc_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1109_, v_keys_1110_, v_vals_1111_, v_i_1112_, v_acc_1113_);
lean_dec_ref(v_vals_1111_);
lean_dec_ref(v_keys_1110_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
if (lean_obj_tag(v_x_1116_) == 0)
{
lean_object* v_es_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1138_; 
v_es_1118_ = lean_ctor_get(v_x_1116_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1116_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1120_ = v_x_1116_;
v_isShared_1121_ = v_isSharedCheck_1138_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_es_1118_);
lean_dec(v_x_1116_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1138_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_array_get_size(v_es_1118_);
v___x_1124_ = lean_nat_dec_lt(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v_es_1118_);
lean_dec_ref(v_f_1115_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
lean_ctor_set(v___x_1120_, 0, v_x_1117_);
v___x_1126_ = v___x_1120_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_x_1117_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_le(v___x_1123_, v___x_1123_);
if (v___x_1128_ == 0)
{
if (v___x_1124_ == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref(v_es_1118_);
lean_dec_ref(v_f_1115_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 1);
lean_ctor_set(v___x_1120_, 0, v_x_1117_);
v___x_1130_ = v___x_1120_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_x_1117_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; 
lean_del_object(v___x_1120_);
v___x_1132_ = ((size_t)0ULL);
v___x_1133_ = lean_usize_of_nat(v___x_1123_);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1115_, v_es_1118_, v___x_1132_, v___x_1133_, v_x_1117_);
lean_dec_ref(v_es_1118_);
return v___x_1134_;
}
}
else
{
size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
lean_del_object(v___x_1120_);
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = lean_usize_of_nat(v___x_1123_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1115_, v_es_1118_, v___x_1135_, v___x_1136_, v_x_1117_);
lean_dec_ref(v_es_1118_);
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_ks_1139_; lean_object* v_vs_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_ks_1139_ = lean_ctor_get(v_x_1116_, 0);
lean_inc_ref(v_ks_1139_);
v_vs_1140_ = lean_ctor_get(v_x_1116_, 1);
lean_inc_ref(v_vs_1140_);
lean_dec_ref(v_x_1116_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1115_, v_ks_1139_, v_vs_1140_, v___x_1141_, v_x_1117_);
lean_dec_ref(v_vs_1140_);
lean_dec_ref(v_ks_1139_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1143_, lean_object* v_as_1144_, size_t v_i_1145_, size_t v_stop_1146_, lean_object* v_b_1147_){
_start:
{
lean_object* v_a_1149_; lean_object* v___y_1154_; uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_eq(v_i_1145_, v_stop_1146_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_array_uget_borrowed(v_as_1144_, v_i_1145_);
switch(lean_obj_tag(v___x_1157_))
{
case 0:
{
lean_object* v_key_1158_; lean_object* v_val_1159_; lean_object* v___x_1160_; 
v_key_1158_ = lean_ctor_get(v___x_1157_, 0);
v_val_1159_ = lean_ctor_get(v___x_1157_, 1);
lean_inc_ref(v_f_1143_);
lean_inc(v_val_1159_);
lean_inc(v_key_1158_);
v___x_1160_ = lean_apply_3(v_f_1143_, v_b_1147_, v_key_1158_, v_val_1159_);
v___y_1154_ = v___x_1160_;
goto v___jp_1153_;
}
case 1:
{
lean_object* v_node_1161_; lean_object* v___x_1162_; 
v_node_1161_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_node_1161_);
lean_inc_ref(v_f_1143_);
v___x_1162_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1143_, v_node_1161_, v_b_1147_);
v___y_1154_ = v___x_1162_;
goto v___jp_1153_;
}
default: 
{
v_a_1149_ = v_b_1147_;
goto v___jp_1148_;
}
}
}
else
{
lean_object* v___x_1163_; 
lean_dec_ref(v_f_1143_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_b_1147_);
return v___x_1163_;
}
v___jp_1148_:
{
size_t v___x_1150_; size_t v___x_1151_; 
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1145_, v___x_1150_);
v_i_1145_ = v___x_1151_;
v_b_1147_ = v_a_1149_;
goto _start;
}
v___jp_1153_:
{
if (lean_obj_tag(v___y_1154_) == 0)
{
lean_dec_ref(v_f_1143_);
return v___y_1154_;
}
else
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___y_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v___y_1154_);
v_a_1149_ = v_a_1155_;
goto v___jp_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1164_, lean_object* v_as_1165_, lean_object* v_i_1166_, lean_object* v_stop_1167_, lean_object* v_b_1168_){
_start:
{
size_t v_i_boxed_1169_; size_t v_stop_boxed_1170_; lean_object* v_res_1171_; 
v_i_boxed_1169_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_stop_boxed_1170_ = lean_unbox_usize(v_stop_1167_);
lean_dec(v_stop_1167_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1164_, v_as_1165_, v_i_boxed_1169_, v_stop_boxed_1170_, v_b_1168_);
lean_dec_ref(v_as_1165_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1172_, lean_object* v_s_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_a_1174_);
lean_ctor_set(v___x_1176_, 1, v_b_1175_);
v___x_1177_ = lean_apply_2(v_f_1172_, v___x_1176_, v_s_1173_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1177_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1177_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1194_, lean_object* v_init_1195_, lean_object* v_f_1196_){
_start:
{
lean_object* v___f_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; 
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1197_, 0, v_f_1196_);
lean_inc_ref(v_map_1194_);
v___x_1198_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1197_, v_map_1194_, v_init_1195_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref(v___x_1198_);
return v_a_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1200_, lean_object* v_init_1201_, lean_object* v_f_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1200_, v_init_1201_, v_f_1202_);
lean_dec_ref(v_map_1200_);
return v_res_1203_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1204_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1207_, lean_object* v_a_1208_, uint8_t v___x_1209_, lean_object* v_as_x27_1210_, lean_object* v_b_1211_){
_start:
{
if (lean_obj_tag(v_as_x27_1210_) == 0)
{
lean_dec(v_a_1208_);
lean_dec_ref(v_tactics_1207_);
return v_b_1211_;
}
else
{
lean_object* v_head_1212_; lean_object* v_fst_1213_; lean_object* v_info_1214_; lean_object* v_tail_1215_; lean_object* v_collectKinds_1216_; lean_object* v___x_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_head_1212_ = lean_ctor_get(v_as_x27_1210_, 0);
v_fst_1213_ = lean_ctor_get(v_head_1212_, 0);
v_info_1214_ = lean_ctor_get(v_fst_1213_, 0);
v_tail_1215_ = lean_ctor_get(v_as_x27_1210_, 1);
v_collectKinds_1216_ = lean_ctor_get(v_info_1214_, 1);
v___x_1217_ = lean_box(v___x_1209_);
lean_inc(v_a_1208_);
lean_inc_ref(v_tactics_1207_);
v___f_1218_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1218_, 0, v_tactics_1207_);
lean_closure_set(v___f_1218_, 1, v_a_1208_);
lean_closure_set(v___f_1218_, 2, v___x_1217_);
v___x_1219_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1216_);
v___x_1220_ = lean_apply_1(v_collectKinds_1216_, v___x_1219_);
v___x_1221_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1220_, v_b_1211_, v___f_1218_);
lean_dec_ref(v___x_1220_);
v_as_x27_1210_ = v_tail_1215_;
v_b_1211_ = v___x_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1223_, lean_object* v_a_1224_, lean_object* v___x_1225_, lean_object* v_as_x27_1226_, lean_object* v_b_1227_){
_start:
{
uint8_t v___x_4416__boxed_1228_; lean_object* v_res_1229_; 
v___x_4416__boxed_1228_ = lean_unbox(v___x_1225_);
v_res_1229_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1223_, v_a_1224_, v___x_4416__boxed_1228_, v_as_x27_1226_, v_b_1227_);
lean_dec(v_as_x27_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1233_, lean_object* v_init_1234_, lean_object* v_x_1235_){
_start:
{
if (lean_obj_tag(v_x_1235_) == 0)
{
lean_object* v_k_1236_; lean_object* v_v_1237_; lean_object* v_l_1238_; lean_object* v_r_1239_; lean_object* v___x_1240_; lean_object* v_a_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_k_1236_ = lean_ctor_get(v_x_1235_, 1);
lean_inc(v_k_1236_);
v_v_1237_ = lean_ctor_get(v_x_1235_, 2);
lean_inc(v_v_1237_);
v_l_1238_ = lean_ctor_get(v_x_1235_, 3);
lean_inc(v_l_1238_);
v_r_1239_ = lean_ctor_get(v_x_1235_, 4);
lean_inc(v_r_1239_);
lean_dec_ref(v_x_1235_);
lean_inc_ref(v_tactics_1233_);
v___x_1240_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1233_, v_init_1234_, v_l_1238_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
v___x_1242_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1243_ = lean_name_eq(v_k_1236_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec_ref(v___x_1240_);
lean_inc_ref(v_tactics_1233_);
v___x_1244_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1233_, v_k_1236_, v___x_1243_, v_v_1237_, v_a_1241_);
lean_dec(v_v_1237_);
v_init_1234_ = v___x_1244_;
v_x_1235_ = v_r_1239_;
goto _start;
}
else
{
lean_object* v_a_1246_; 
lean_dec(v_a_1241_);
lean_dec(v_v_1237_);
lean_dec(v_k_1236_);
v_a_1246_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1240_);
v_init_1234_ = v_a_1246_;
v_x_1235_ = v_r_1239_;
goto _start;
}
}
else
{
lean_object* v___x_1248_; 
lean_dec_ref(v_tactics_1233_);
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_init_1234_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1249_, lean_object* v_table_1250_, lean_object* v_firsts_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v_a_1253_; 
v___x_1252_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1249_, v_firsts_1251_, v_table_1250_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1252_);
return v_a_1253_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1255_, v_x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_){
_start:
{
uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1258_, v_x_1259_, v_x_1260_);
lean_dec(v_x_1260_);
lean_dec_ref(v_x_1259_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1263_, lean_object* v_k_1264_, lean_object* v_t_1265_, lean_object* v_hl_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1263_, v_k_1264_, v_t_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1268_, lean_object* v_00_u03b2_1269_, lean_object* v_map_1270_, lean_object* v_init_1271_, lean_object* v_f_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1270_, v_init_1271_, v_f_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_map_1276_, lean_object* v_init_1277_, lean_object* v_f_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1274_, v_00_u03b2_1275_, v_map_1276_, v_init_1277_, v_f_1278_);
lean_dec_ref(v_map_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1280_, lean_object* v_a_1281_, uint8_t v___x_1282_, lean_object* v_as_1283_, lean_object* v_as_x27_1284_, lean_object* v_b_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1280_, v_a_1281_, v___x_1282_, v_as_x27_1284_, v_b_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1288_, lean_object* v_a_1289_, lean_object* v___x_1290_, lean_object* v_as_1291_, lean_object* v_as_x27_1292_, lean_object* v_b_1293_, lean_object* v_a_1294_){
_start:
{
uint8_t v___x_4499__boxed_1295_; lean_object* v_res_1296_; 
v___x_4499__boxed_1295_ = lean_unbox(v___x_1290_);
v_res_1296_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1288_, v_a_1289_, v___x_4499__boxed_1295_, v_as_1291_, v_as_x27_1292_, v_b_1293_, v_a_1294_);
lean_dec(v_as_x27_1292_);
lean_dec(v_as_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1297_, lean_object* v_x_1298_, size_t v_x_1299_, lean_object* v_x_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1298_, v_x_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
size_t v_x_4508__boxed_1306_; uint8_t v_res_1307_; lean_object* v_r_1308_; 
v_x_4508__boxed_1306_ = lean_unbox_usize(v_x_1304_);
lean_dec(v_x_1304_);
v_res_1307_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1302_, v_x_1303_, v_x_4508__boxed_1306_, v_x_1305_);
lean_dec(v_x_1305_);
lean_dec_ref(v_x_1303_);
v_r_1308_ = lean_box(v_res_1307_);
return v_r_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1309_, lean_object* v_f_1310_, lean_object* v_init_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1310_, v_map_1309_, v_init_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1313_, lean_object* v_00_u03c3_1314_, lean_object* v_00_u03b2_1315_, lean_object* v_map_1316_, lean_object* v_f_1317_, lean_object* v_init_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1317_, v_map_1316_, v_init_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1320_, lean_object* v_keys_1321_, lean_object* v_vals_1322_, lean_object* v_heq_1323_, lean_object* v_i_1324_, lean_object* v_k_1325_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1321_, v_i_1324_, v_k_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1327_, lean_object* v_keys_1328_, lean_object* v_vals_1329_, lean_object* v_heq_1330_, lean_object* v_i_1331_, lean_object* v_k_1332_){
_start:
{
uint8_t v_res_1333_; lean_object* v_r_1334_; 
v_res_1333_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1327_, v_keys_1328_, v_vals_1329_, v_heq_1330_, v_i_1331_, v_k_1332_);
lean_dec(v_k_1332_);
lean_dec_ref(v_vals_1329_);
lean_dec_ref(v_keys_1328_);
v_r_1334_ = lean_box(v_res_1333_);
return v_r_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1335_, lean_object* v_00_u03c3_1336_, lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_f_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1339_, v_x_1340_, v_x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1343_, lean_object* v_00_u03b2_1344_, lean_object* v_00_u03c3_1345_, lean_object* v_00_u03c3_1346_, lean_object* v_f_1347_, lean_object* v_as_1348_, size_t v_i_1349_, size_t v_stop_1350_, lean_object* v_b_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1347_, v_as_1348_, v_i_1349_, v_stop_1350_, v_b_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_00_u03c3_1355_, lean_object* v_00_u03c3_1356_, lean_object* v_f_1357_, lean_object* v_as_1358_, lean_object* v_i_1359_, lean_object* v_stop_1360_, lean_object* v_b_1361_){
_start:
{
size_t v_i_boxed_1362_; size_t v_stop_boxed_1363_; lean_object* v_res_1364_; 
v_i_boxed_1362_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_stop_boxed_1363_ = lean_unbox_usize(v_stop_1360_);
lean_dec(v_stop_1360_);
v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1353_, v_00_u03b2_1354_, v_00_u03c3_1355_, v_00_u03c3_1356_, v_f_1357_, v_as_1358_, v_i_boxed_1362_, v_stop_boxed_1363_, v_b_1361_);
lean_dec_ref(v_as_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1365_, lean_object* v_00_u03c3_1366_, lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_f_1369_, lean_object* v_keys_1370_, lean_object* v_vals_1371_, lean_object* v_heq_1372_, lean_object* v_i_1373_, lean_object* v_acc_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1369_, v_keys_1370_, v_vals_1371_, v_i_1373_, v_acc_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1376_, lean_object* v_00_u03c3_1377_, lean_object* v_00_u03b1_1378_, lean_object* v_00_u03b2_1379_, lean_object* v_f_1380_, lean_object* v_keys_1381_, lean_object* v_vals_1382_, lean_object* v_heq_1383_, lean_object* v_i_1384_, lean_object* v_acc_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1376_, v_00_u03c3_1377_, v_00_u03b1_1378_, v_00_u03b2_1379_, v_f_1380_, v_keys_1381_, v_vals_1382_, v_heq_1383_, v_i_1384_, v_acc_1385_);
lean_dec_ref(v_vals_1382_);
lean_dec_ref(v_keys_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1387_, lean_object* v_x2_1388_){
_start:
{
lean_object* v_fst_1389_; lean_object* v_snd_1390_; lean_object* v___x_1391_; 
v_fst_1389_ = lean_ctor_get(v_x2_1388_, 0);
lean_inc(v_fst_1389_);
v_snd_1390_ = lean_ctor_get(v_x2_1388_, 1);
lean_inc(v_snd_1390_);
lean_dec_ref(v_x2_1388_);
v___x_1391_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1389_, v_snd_1390_, v_x1_1387_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1411_, lean_object* v_x1_1412_, lean_object* v_x2_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_array_get_size(v_x2_1413_);
v___x_1416_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1417_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
if (v___x_1417_ == 0)
{
lean_dec_ref(v_x2_1413_);
lean_dec_ref(v___f_1411_);
return v_x1_1412_;
}
else
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_nat_dec_le(v___x_1415_, v___x_1415_);
if (v___x_1418_ == 0)
{
if (v___x_1417_ == 0)
{
lean_dec_ref(v_x2_1413_);
lean_dec_ref(v___f_1411_);
return v_x1_1412_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1415_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1416_, v___f_1411_, v_x2_1413_, v___x_1419_, v___x_1420_, v_x1_1412_);
return v___x_1421_;
}
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1415_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1416_, v___f_1411_, v_x2_1413_, v___x_1422_, v___x_1423_, v_x1_1412_);
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v___x_1431_, lean_object* v___x_1432_, lean_object* v_toPure_1433_, lean_object* v___f_1434_, lean_object* v_env_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v_ext_1437_; lean_object* v_toEnvExtension_1438_; lean_object* v_asyncMode_1439_; lean_object* v___x_1440_; lean_object* v_categories_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1436_ = l_Lean_Parser_parserExtension;
v_ext_1437_ = lean_ctor_get(v___x_1436_, 1);
v_toEnvExtension_1438_ = lean_ctor_get(v_ext_1437_, 0);
v_asyncMode_1439_ = lean_ctor_get(v_toEnvExtension_1438_, 2);
lean_inc_ref(v_env_1435_);
v___x_1440_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1428_, v___x_1436_, v_env_1435_, v_asyncMode_1439_);
v_categories_1441_ = lean_ctor_get(v___x_1440_, 2);
lean_inc_ref(v_categories_1441_);
lean_dec(v___x_1440_);
v___x_1442_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1443_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1429_, v___x_1430_, v_categories_1441_, v___x_1442_);
lean_dec_ref(v_categories_1441_);
if (lean_obj_tag(v___x_1443_) == 1)
{
lean_object* v_val_1444_; lean_object* v___y_1446_; lean_object* v___x_1453_; lean_object* v_toEnvExtension_1454_; lean_object* v_exportEntriesFn_1455_; lean_object* v_asyncMode_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_importedEntries_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v_exported_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_val_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_val_1444_);
lean_dec_ref(v___x_1443_);
v___x_1453_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1454_ = lean_ctor_get(v___x_1453_, 0);
v_exportEntriesFn_1455_ = lean_ctor_get(v___x_1453_, 4);
v_asyncMode_1456_ = lean_ctor_get(v_toEnvExtension_1454_, 2);
v___x_1457_ = lean_box(0);
lean_inc_ref_n(v_env_1435_, 2);
v___x_1458_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1431_, v_toEnvExtension_1454_, v_env_1435_, v_asyncMode_1456_, v___x_1457_);
v_importedEntries_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc_ref(v_importedEntries_1459_);
lean_dec(v___x_1458_);
v___x_1460_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1432_, v___x_1453_, v_env_1435_, v_asyncMode_1456_, v___x_1457_);
lean_inc_ref(v_exportEntriesFn_1455_);
v___x_1461_ = lean_apply_2(v_exportEntriesFn_1455_, v_env_1435_, v___x_1460_);
v_exported_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_exported_1462_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = lean_box(1);
v___x_1464_ = lean_array_push(v_importedEntries_1459_, v_exported_1462_);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = lean_array_get_size(v___x_1464_);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1468_ = lean_nat_dec_lt(v___x_1465_, v___x_1466_);
if (v___x_1468_ == 0)
{
lean_dec_ref(v___x_1464_);
lean_dec_ref(v___f_1434_);
v___y_1446_ = v___x_1463_;
goto v___jp_1445_;
}
else
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_nat_dec_le(v___x_1466_, v___x_1466_);
if (v___x_1469_ == 0)
{
if (v___x_1468_ == 0)
{
lean_dec_ref(v___x_1464_);
lean_dec_ref(v___f_1434_);
v___y_1446_ = v___x_1463_;
goto v___jp_1445_;
}
else
{
size_t v___x_1470_; size_t v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = ((size_t)0ULL);
v___x_1471_ = lean_usize_of_nat(v___x_1466_);
v___x_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1467_, v___f_1434_, v___x_1464_, v___x_1470_, v___x_1471_, v___x_1463_);
v___y_1446_ = v___x_1472_;
goto v___jp_1445_;
}
}
else
{
size_t v___x_1473_; size_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = ((size_t)0ULL);
v___x_1474_ = lean_usize_of_nat(v___x_1466_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1467_, v___f_1434_, v___x_1464_, v___x_1473_, v___x_1474_, v___x_1463_);
v___y_1446_ = v___x_1475_;
goto v___jp_1445_;
}
}
v___jp_1445_:
{
lean_object* v_tables_1447_; lean_object* v_leadingTable_1448_; lean_object* v_trailingTable_1449_; lean_object* v_firstTokens_1450_; lean_object* v_firstTokens_1451_; lean_object* v___x_1452_; 
v_tables_1447_ = lean_ctor_get(v_val_1444_, 2);
v_leadingTable_1448_ = lean_ctor_get(v_tables_1447_, 0);
v_trailingTable_1449_ = lean_ctor_get(v_tables_1447_, 2);
lean_inc(v_trailingTable_1449_);
lean_inc(v_leadingTable_1448_);
lean_inc(v_val_1444_);
v_firstTokens_1450_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1444_, v_leadingTable_1448_, v___y_1446_);
v_firstTokens_1451_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1444_, v_trailingTable_1449_, v_firstTokens_1450_);
v___x_1452_ = lean_apply_2(v_toPure_1433_, lean_box(0), v_firstTokens_1451_);
return v___x_1452_;
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec(v___x_1443_);
lean_dec_ref(v_env_1435_);
lean_dec_ref(v___f_1434_);
lean_dec(v___x_1432_);
v___x_1476_ = lean_box(1);
v___x_1477_ = lean_apply_2(v_toPure_1433_, lean_box(0), v___x_1476_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v_toPure_1483_, lean_object* v___f_1484_, lean_object* v_env_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1478_, v___x_1479_, v___x_1480_, v___x_1481_, v___x_1482_, v_toPure_1483_, v___f_1484_, v_env_1485_);
lean_dec_ref(v___x_1481_);
lean_dec_ref(v___x_1478_);
return v_res_1486_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_box(1);
v___x_1491_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1494_, lean_object* v_inst_1495_){
_start:
{
lean_object* v_toApplicative_1496_; lean_object* v_toBind_1497_; lean_object* v_getEnv_1498_; lean_object* v_toPure_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___f_1506_; lean_object* v___x_1507_; 
v_toApplicative_1496_ = lean_ctor_get(v_inst_1494_, 0);
lean_inc_ref(v_toApplicative_1496_);
v_toBind_1497_ = lean_ctor_get(v_inst_1494_, 1);
lean_inc(v_toBind_1497_);
lean_dec_ref(v_inst_1494_);
v_getEnv_1498_ = lean_ctor_get(v_inst_1495_, 0);
lean_inc(v_getEnv_1498_);
lean_dec_ref(v_inst_1495_);
v_toPure_1499_ = lean_ctor_get(v_toApplicative_1496_, 1);
lean_inc(v_toPure_1499_);
lean_dec_ref(v_toApplicative_1496_);
v___f_1500_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1501_ = lean_box(1);
v___x_1502_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1504_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1505_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1506_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1506_, 0, v___x_1505_);
lean_closure_set(v___f_1506_, 1, v___x_1503_);
lean_closure_set(v___f_1506_, 2, v___x_1504_);
lean_closure_set(v___f_1506_, 3, v___x_1502_);
lean_closure_set(v___f_1506_, 4, v___x_1501_);
lean_closure_set(v___f_1506_, 5, v_toPure_1499_);
lean_closure_set(v___f_1506_, 6, v___f_1500_);
v___x_1507_ = lean_apply_4(v_toBind_1497_, lean_box(0), lean_box(0), v_getEnv_1498_, v___f_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1509_, v_inst_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_x_1512_, lean_object* v_y_1513_){
_start:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_nat_dec_lt(v_x_1512_, v_y_1513_);
if (v___x_1514_ == 0)
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_nat_dec_eq(v_x_1512_, v_y_1513_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = 2;
return v___x_1516_;
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = 1;
return v___x_1517_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed(lean_object* v_x_1519_, lean_object* v_y_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(v_x_1519_, v_y_1520_);
lean_dec(v_y_1520_);
lean_dec(v_x_1519_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v___f_1523_, lean_object* v_a_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_fst_1527_; lean_object* v_snd_1528_; lean_object* v_r_1529_; lean_object* v___x_1530_; 
v_fst_1527_ = lean_ctor_get(v_a_1524_, 0);
lean_inc(v_fst_1527_);
v_snd_1528_ = lean_ctor_get(v_a_1524_, 1);
lean_inc(v_snd_1528_);
lean_dec_ref(v_a_1524_);
v_r_1529_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_1523_, v_fst_1527_, v_snd_1528_, v___y_1526_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_r_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2(lean_object* v_n_1537_, lean_object* v___y_1538_, lean_object* v___f_1539_, lean_object* v_toPure_1540_, lean_object* v_firsts_1541_, lean_object* v_____do__lift_1542_){
_start:
{
lean_object* v___y_1544_; lean_object* v_val_1576_; 
if (lean_obj_tag(v_____do__lift_1542_) == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3));
lean_inc(v_n_1537_);
v___x_1579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1578_, v_firsts_1541_, v_n_1537_);
if (lean_obj_tag(v___x_1579_) == 0)
{
uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = 1;
lean_inc(v_n_1537_);
v___x_1581_ = l_Lean_Name_toString(v_n_1537_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
v___y_1544_ = v___x_1582_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1583_; 
v_val_1583_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_val_1583_);
lean_dec_ref(v___x_1579_);
v_val_1576_ = v_val_1583_;
goto v___jp_1575_;
}
}
else
{
lean_object* v_val_1584_; 
lean_dec(v_firsts_1541_);
v_val_1584_ = lean_ctor_get(v_____do__lift_1542_, 0);
lean_inc(v_val_1584_);
lean_dec_ref(v_____do__lift_1542_);
v_val_1576_ = v_val_1584_;
goto v___jp_1575_;
}
v___jp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v_r_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___y_1544_);
v___x_1548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1545_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1545_);
v___x_1550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_1551_ = lean_box(2);
v___x_1552_ = 1;
lean_inc_n(v_n_1537_, 3);
v___x_1553_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1537_, v___x_1552_);
v___x_1554_ = lean_string_utf8_byte_size(v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1546_);
lean_ctor_set(v___x_1555_, 2, v___x_1554_);
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_n_1537_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v___x_1556_);
v___x_1559_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1551_);
lean_ctor_set(v___x_1559_, 1, v___x_1555_);
lean_ctor_set(v___x_1559_, 2, v_n_1537_);
lean_ctor_set(v___x_1559_, 3, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1550_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = l_Lean_LocalContext_empty;
v___x_1562_ = lean_box(0);
v___x_1563_ = l_Lean_Expr_const___override(v_n_1537_, v___y_1538_);
v___x_1564_ = 0;
v___x_1565_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1565_, 0, v___x_1560_);
lean_ctor_set(v___x_1565_, 1, v___x_1561_);
lean_ctor_set(v___x_1565_, 2, v___x_1562_);
lean_ctor_set(v___x_1565_, 3, v___x_1563_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*4, v___x_1564_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*4 + 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1546_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1556_);
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v_r_1570_ = lean_box(1);
v___x_1571_ = l_List_forIn_x27_loop___redArg(v___x_1569_, v___f_1539_, v___x_1568_, v_r_1570_);
lean_dec_ref(v___x_1568_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1549_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
v___x_1574_ = lean_apply_2(v_toPure_1540_, lean_box(0), v___x_1573_);
return v___x_1574_;
}
v___jp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1577_, 0, v_val_1576_);
v___y_1544_ = v___x_1577_;
goto v___jp_1543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3(lean_object* v_n_1585_, lean_object* v___f_1586_, lean_object* v_toPure_1587_, lean_object* v_firsts_1588_, lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_toBind_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___f_1594_, lean_object* v_env_1595_){
_start:
{
lean_object* v___y_1597_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = l_Lean_Environment_constants(v_env_1595_);
lean_inc(v_n_1585_);
v___x_1602_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1592_, v___x_1593_, v___x_1601_, v_n_1585_);
lean_dec_ref(v___x_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v___x_1603_; 
lean_dec_ref(v___f_1594_);
v___x_1603_ = lean_box(0);
v___y_1597_ = v___x_1603_;
goto v___jp_1596_;
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_val_1604_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_val_1604_);
lean_dec_ref(v___x_1602_);
v___x_1605_ = l_Lean_ConstantInfo_levelParams(v_val_1604_);
lean_dec(v_val_1604_);
v___x_1606_ = lean_box(0);
v___x_1607_ = l_List_mapTR_loop___redArg(v___f_1594_, v___x_1605_, v___x_1606_);
v___y_1597_ = v___x_1607_;
goto v___jp_1596_;
}
v___jp_1596_:
{
lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_inc(v_n_1585_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1598_, 0, v_n_1585_);
lean_closure_set(v___f_1598_, 1, v___y_1597_);
lean_closure_set(v___f_1598_, 2, v___f_1586_);
lean_closure_set(v___f_1598_, 3, v_toPure_1587_);
lean_closure_set(v___f_1598_, 4, v_firsts_1588_);
v___x_1599_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1589_, v_inst_1590_, v_n_1585_);
v___x_1600_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v___x_1599_, v___f_1598_);
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_firsts_1614_, lean_object* v_n_1615_){
_start:
{
lean_object* v_toApplicative_1616_; lean_object* v_toBind_1617_; lean_object* v_getEnv_1618_; lean_object* v_toPure_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___f_1624_; lean_object* v___x_1625_; 
v_toApplicative_1616_ = lean_ctor_get(v_inst_1612_, 0);
v_toBind_1617_ = lean_ctor_get(v_inst_1612_, 1);
lean_inc_n(v_toBind_1617_, 2);
v_getEnv_1618_ = lean_ctor_get(v_inst_1613_, 0);
lean_inc(v_getEnv_1618_);
v_toPure_1619_ = lean_ctor_get(v_toApplicative_1616_, 1);
lean_inc(v_toPure_1619_);
v___f_1620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1));
v___f_1621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2));
v___x_1622_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1623_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1624_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3), 11, 10);
lean_closure_set(v___f_1624_, 0, v_n_1615_);
lean_closure_set(v___f_1624_, 1, v___f_1620_);
lean_closure_set(v___f_1624_, 2, v_toPure_1619_);
lean_closure_set(v___f_1624_, 3, v_firsts_1614_);
lean_closure_set(v___f_1624_, 4, v_inst_1612_);
lean_closure_set(v___f_1624_, 5, v_inst_1613_);
lean_closure_set(v___f_1624_, 6, v_toBind_1617_);
lean_closure_set(v___f_1624_, 7, v___x_1622_);
lean_closure_set(v___f_1624_, 8, v___x_1623_);
lean_closure_set(v___f_1624_, 9, v___f_1621_);
v___x_1625_ = lean_apply_4(v_toBind_1617_, lean_box(0), lean_box(0), v_getEnv_1618_, v___f_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_firsts_1629_, lean_object* v_n_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1627_, v_inst_1628_, v_firsts_1629_, v_n_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1636_);
lean_dec_ref(v_s_1636_);
return v_res_1637_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1638_, lean_object* v_x1_1639_, lean_object* v_x2_1640_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1641_ = l_Lean_Name_toString(v_x1_1639_, v___x_1638_);
v___x_1642_ = l_Lean_Name_toString(v_x2_1640_, v___x_1638_);
v___x_1643_ = lean_string_dec_lt(v___x_1641_, v___x_1642_);
lean_dec_ref(v___x_1642_);
lean_dec_ref(v___x_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1644_, lean_object* v_x1_1645_, lean_object* v_x2_1646_){
_start:
{
uint8_t v___x_18299__boxed_1647_; uint8_t v_res_1648_; lean_object* v_r_1649_; 
v___x_18299__boxed_1647_ = lean_unbox(v___x_1644_);
v_res_1648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_18299__boxed_1647_, v_x1_1645_, v_x2_1646_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(lean_object* v_hi_1650_, lean_object* v_pivot_1651_, lean_object* v_as_1652_, lean_object* v_i_1653_, lean_object* v_k_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_nat_dec_lt(v_k_1654_, v_hi_1650_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v_k_1654_);
lean_dec(v_pivot_1651_);
v___x_1656_ = lean_array_fswap(v_as_1652_, v_i_1653_, v_hi_1650_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v_i_1653_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1658_ = lean_array_fget_borrowed(v_as_1652_, v_k_1654_);
lean_inc(v___x_1658_);
v___x_1659_ = l_Lean_Name_toString(v___x_1658_, v___x_1655_);
lean_inc(v_pivot_1651_);
v___x_1660_ = l_Lean_Name_toString(v_pivot_1651_, v___x_1655_);
v___x_1661_ = lean_string_dec_lt(v___x_1659_, v___x_1660_);
lean_dec_ref(v___x_1660_);
lean_dec_ref(v___x_1659_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = lean_nat_add(v_k_1654_, v___x_1662_);
lean_dec(v_k_1654_);
v_k_1654_ = v___x_1663_;
goto _start;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1665_ = lean_array_fswap(v_as_1652_, v_i_1653_, v_k_1654_);
v___x_1666_ = lean_unsigned_to_nat(1u);
v___x_1667_ = lean_nat_add(v_i_1653_, v___x_1666_);
lean_dec(v_i_1653_);
v___x_1668_ = lean_nat_add(v_k_1654_, v___x_1666_);
lean_dec(v_k_1654_);
v_as_1652_ = v___x_1665_;
v_i_1653_ = v___x_1667_;
v_k_1654_ = v___x_1668_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg___boxed(lean_object* v_hi_1670_, lean_object* v_pivot_1671_, lean_object* v_as_1672_, lean_object* v_i_1673_, lean_object* v_k_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(v_hi_1670_, v_pivot_1671_, v_as_1672_, v_i_1673_, v_k_1674_);
lean_dec(v_hi_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1676_, lean_object* v_as_1677_, lean_object* v_lo_1678_, lean_object* v_hi_1679_){
_start:
{
lean_object* v___y_1681_; uint8_t v___x_1691_; 
v___x_1691_ = lean_nat_dec_lt(v_lo_1678_, v_hi_1679_);
if (v___x_1691_ == 0)
{
lean_dec(v_lo_1678_);
return v_as_1677_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v_mid_1694_; lean_object* v___y_1696_; lean_object* v___y_1702_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1692_ = lean_nat_add(v_lo_1678_, v_hi_1679_);
v___x_1693_ = lean_unsigned_to_nat(1u);
v_mid_1694_ = lean_nat_shiftr(v___x_1692_, v___x_1693_);
lean_dec(v___x_1692_);
v___x_1707_ = lean_array_fget_borrowed(v_as_1677_, v_mid_1694_);
v___x_1708_ = lean_array_fget_borrowed(v_as_1677_, v_lo_1678_);
lean_inc(v___x_1708_);
lean_inc(v___x_1707_);
v___x_1709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1691_, v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
v___y_1702_ = v_as_1677_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_array_fswap(v_as_1677_, v_lo_1678_, v_mid_1694_);
v___y_1702_ = v___x_1710_;
goto v___jp_1701_;
}
v___jp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1697_ = lean_array_fget_borrowed(v___y_1696_, v_mid_1694_);
v___x_1698_ = lean_array_fget_borrowed(v___y_1696_, v_hi_1679_);
lean_inc(v___x_1698_);
lean_inc(v___x_1697_);
v___x_1699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1691_, v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec(v_mid_1694_);
v___y_1681_ = v___y_1696_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_array_fswap(v___y_1696_, v_mid_1694_, v_hi_1679_);
lean_dec(v_mid_1694_);
v___y_1681_ = v___x_1700_;
goto v___jp_1680_;
}
}
v___jp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1703_ = lean_array_fget_borrowed(v___y_1702_, v_hi_1679_);
v___x_1704_ = lean_array_fget_borrowed(v___y_1702_, v_lo_1678_);
lean_inc(v___x_1704_);
lean_inc(v___x_1703_);
v___x_1705_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1691_, v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
v___y_1696_ = v___y_1702_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_array_fswap(v___y_1702_, v_lo_1678_, v_hi_1679_);
v___y_1696_ = v___x_1706_;
goto v___jp_1695_;
}
}
}
v___jp_1680_:
{
lean_object* v_pivot_1682_; lean_object* v___x_1683_; lean_object* v_fst_1684_; lean_object* v_snd_1685_; uint8_t v___x_1686_; 
v_pivot_1682_ = lean_array_fget(v___y_1681_, v_hi_1679_);
lean_inc_n(v_lo_1678_, 2);
v___x_1683_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(v_hi_1679_, v_pivot_1682_, v___y_1681_, v_lo_1678_, v_lo_1678_);
v_fst_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_fst_1684_);
v_snd_1685_ = lean_ctor_get(v___x_1683_, 1);
lean_inc(v_snd_1685_);
lean_dec_ref(v___x_1683_);
v___x_1686_ = lean_nat_dec_le(v_hi_1679_, v_fst_1684_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1676_, v_snd_1685_, v_lo_1678_, v_fst_1684_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_nat_add(v_fst_1684_, v___x_1688_);
lean_dec(v_fst_1684_);
v_as_1677_ = v___x_1687_;
v_lo_1678_ = v___x_1689_;
goto _start;
}
else
{
lean_dec(v_fst_1684_);
lean_dec(v_lo_1678_);
return v_snd_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1711_, lean_object* v_as_1712_, lean_object* v_lo_1713_, lean_object* v_hi_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1711_, v_as_1712_, v_lo_1713_, v_hi_1714_);
lean_dec(v_hi_1714_);
lean_dec(v_n_1711_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(lean_object* v_a_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_box(0);
return v___x_1718_;
}
else
{
lean_object* v_key_1719_; lean_object* v_value_1720_; lean_object* v_tail_1721_; uint8_t v___x_1722_; 
v_key_1719_ = lean_ctor_get(v_x_1717_, 0);
v_value_1720_ = lean_ctor_get(v_x_1717_, 1);
v_tail_1721_ = lean_ctor_get(v_x_1717_, 2);
v___x_1722_ = lean_name_eq(v_key_1719_, v_a_1716_);
if (v___x_1722_ == 0)
{
v_x_1717_ = v_tail_1721_;
goto _start;
}
else
{
lean_object* v___x_1724_; 
lean_inc(v_value_1720_);
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_value_1720_);
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg___boxed(lean_object* v_a_1725_, lean_object* v_x_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1725_, v_x_1726_);
lean_dec(v_x_1726_);
lean_dec(v_a_1725_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(lean_object* v_m_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_buckets_1730_; lean_object* v___x_1731_; uint64_t v___y_1733_; 
v_buckets_1730_ = lean_ctor_get(v_m_1728_, 1);
v___x_1731_ = lean_array_get_size(v_buckets_1730_);
if (lean_obj_tag(v_a_1729_) == 0)
{
uint64_t v___x_1747_; 
v___x_1747_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1733_ = v___x_1747_;
goto v___jp_1732_;
}
else
{
uint64_t v_hash_1748_; 
v_hash_1748_ = lean_ctor_get_uint64(v_a_1729_, sizeof(void*)*2);
v___y_1733_ = v_hash_1748_;
goto v___jp_1732_;
}
v___jp_1732_:
{
uint64_t v___x_1734_; uint64_t v___x_1735_; uint64_t v_fold_1736_; uint64_t v___x_1737_; uint64_t v___x_1738_; uint64_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1734_ = 32ULL;
v___x_1735_ = lean_uint64_shift_right(v___y_1733_, v___x_1734_);
v_fold_1736_ = lean_uint64_xor(v___y_1733_, v___x_1735_);
v___x_1737_ = 16ULL;
v___x_1738_ = lean_uint64_shift_right(v_fold_1736_, v___x_1737_);
v___x_1739_ = lean_uint64_xor(v_fold_1736_, v___x_1738_);
v___x_1740_ = lean_uint64_to_usize(v___x_1739_);
v___x_1741_ = lean_usize_of_nat(v___x_1731_);
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_sub(v___x_1741_, v___x_1742_);
v___x_1744_ = lean_usize_land(v___x_1740_, v___x_1743_);
v___x_1745_ = lean_array_uget_borrowed(v_buckets_1730_, v___x_1744_);
v___x_1746_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1729_, v___x_1745_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg___boxed(lean_object* v_m_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_1749_, v_a_1750_);
lean_dec(v_a_1750_);
lean_dec_ref(v_m_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1752_, lean_object* v_vals_1753_, lean_object* v_i_1754_, lean_object* v_k_1755_){
_start:
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_array_get_size(v_keys_1752_);
v___x_1757_ = lean_nat_dec_lt(v_i_1754_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec(v_i_1754_);
v___x_1758_ = lean_box(0);
return v___x_1758_;
}
else
{
lean_object* v_k_x27_1759_; uint8_t v___x_1760_; 
v_k_x27_1759_ = lean_array_fget_borrowed(v_keys_1752_, v_i_1754_);
v___x_1760_ = lean_name_eq(v_k_1755_, v_k_x27_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = lean_nat_add(v_i_1754_, v___x_1761_);
lean_dec(v_i_1754_);
v_i_1754_ = v___x_1762_;
goto _start;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_array_fget_borrowed(v_vals_1753_, v_i_1754_);
lean_dec(v_i_1754_);
lean_inc(v___x_1764_);
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1766_, lean_object* v_vals_1767_, lean_object* v_i_1768_, lean_object* v_k_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1766_, v_vals_1767_, v_i_1768_, v_k_1769_);
lean_dec(v_k_1769_);
lean_dec_ref(v_vals_1767_);
lean_dec_ref(v_keys_1766_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1771_, size_t v_x_1772_, lean_object* v_x_1773_){
_start:
{
if (lean_obj_tag(v_x_1771_) == 0)
{
lean_object* v_es_1774_; lean_object* v___x_1775_; size_t v___x_1776_; size_t v___x_1777_; size_t v___x_1778_; lean_object* v_j_1779_; lean_object* v___x_1780_; 
v_es_1774_ = lean_ctor_get(v_x_1771_, 0);
v___x_1775_ = lean_box(2);
v___x_1776_ = ((size_t)5ULL);
v___x_1777_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1778_ = lean_usize_land(v_x_1772_, v___x_1777_);
v_j_1779_ = lean_usize_to_nat(v___x_1778_);
v___x_1780_ = lean_array_get_borrowed(v___x_1775_, v_es_1774_, v_j_1779_);
lean_dec(v_j_1779_);
switch(lean_obj_tag(v___x_1780_))
{
case 0:
{
lean_object* v_key_1781_; lean_object* v_val_1782_; uint8_t v___x_1783_; 
v_key_1781_ = lean_ctor_get(v___x_1780_, 0);
v_val_1782_ = lean_ctor_get(v___x_1780_, 1);
v___x_1783_ = lean_name_eq(v_x_1773_, v_key_1781_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_box(0);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; 
lean_inc(v_val_1782_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_val_1782_);
return v___x_1785_;
}
}
case 1:
{
lean_object* v_node_1786_; size_t v___x_1787_; 
v_node_1786_ = lean_ctor_get(v___x_1780_, 0);
v___x_1787_ = lean_usize_shift_right(v_x_1772_, v___x_1776_);
v_x_1771_ = v_node_1786_;
v_x_1772_ = v___x_1787_;
goto _start;
}
default: 
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_box(0);
return v___x_1789_;
}
}
}
else
{
lean_object* v_ks_1790_; lean_object* v_vs_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_ks_1790_ = lean_ctor_get(v_x_1771_, 0);
v_vs_1791_ = lean_ctor_get(v_x_1771_, 1);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1790_, v_vs_1791_, v___x_1792_, v_x_1773_);
return v___x_1793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
size_t v_x_18482__boxed_1797_; lean_object* v_res_1798_; 
v_x_18482__boxed_1797_ = lean_unbox_usize(v_x_1795_);
lean_dec(v_x_1795_);
v_res_1798_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1794_, v_x_18482__boxed_1797_, v_x_1796_);
lean_dec(v_x_1796_);
lean_dec_ref(v_x_1794_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1799_, lean_object* v_x_1800_){
_start:
{
uint64_t v___y_1802_; 
if (lean_obj_tag(v_x_1800_) == 0)
{
uint64_t v___x_1805_; 
v___x_1805_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1802_ = v___x_1805_;
goto v___jp_1801_;
}
else
{
uint64_t v_hash_1806_; 
v_hash_1806_ = lean_ctor_get_uint64(v_x_1800_, sizeof(void*)*2);
v___y_1802_ = v_hash_1806_;
goto v___jp_1801_;
}
v___jp_1801_:
{
size_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_uint64_to_usize(v___y_1802_);
v___x_1804_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1799_, v___x_1803_, v_x_1800_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1807_, v_x_1808_);
lean_dec(v_x_1808_);
lean_dec_ref(v_x_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
uint8_t v_stage_u2081_1812_; 
v_stage_u2081_1812_ = lean_ctor_get_uint8(v_x_1810_, sizeof(void*)*2);
if (v_stage_u2081_1812_ == 0)
{
lean_object* v_map_u2081_1813_; lean_object* v_map_u2082_1814_; lean_object* v___x_1815_; 
v_map_u2081_1813_ = lean_ctor_get(v_x_1810_, 0);
v_map_u2082_1814_ = lean_ctor_get(v_x_1810_, 1);
v___x_1815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1813_, v_x_1811_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1814_, v_x_1811_);
return v___x_1816_;
}
else
{
return v___x_1815_;
}
}
else
{
lean_object* v_map_u2081_1817_; lean_object* v___x_1818_; 
v_map_u2081_1817_ = lean_ctor_get(v_x_1810_, 0);
v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1817_, v_x_1811_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg___boxed(lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_1819_, v_x_1820_);
lean_dec(v_x_1820_);
lean_dec_ref(v_x_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
if (lean_obj_tag(v_a_1822_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = l_List_reverse___redArg(v_a_1823_);
return v___x_1824_;
}
else
{
lean_object* v_head_1825_; lean_object* v_tail_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
v_head_1825_ = lean_ctor_get(v_a_1822_, 0);
v_tail_1826_ = lean_ctor_get(v_a_1822_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_a_1822_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v_a_1822_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_tail_1826_);
lean_inc(v_head_1825_);
lean_dec(v_a_1822_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = l_Lean_Level_param___override(v_head_1825_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v_a_1823_);
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_a_1823_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
v_a_1822_ = v_tail_1826_;
v_a_1823_ = v___x_1832_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(lean_object* v_t_1836_, lean_object* v_k_1837_){
_start:
{
if (lean_obj_tag(v_t_1836_) == 0)
{
lean_object* v_k_1838_; lean_object* v_v_1839_; lean_object* v_l_1840_; lean_object* v_r_1841_; uint8_t v___x_1842_; 
v_k_1838_ = lean_ctor_get(v_t_1836_, 1);
v_v_1839_ = lean_ctor_get(v_t_1836_, 2);
v_l_1840_ = lean_ctor_get(v_t_1836_, 3);
v_r_1841_ = lean_ctor_get(v_t_1836_, 4);
v___x_1842_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1837_, v_k_1838_);
switch(v___x_1842_)
{
case 0:
{
v_t_1836_ = v_l_1840_;
goto _start;
}
case 1:
{
lean_object* v___x_1844_; 
lean_inc(v_v_1839_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_v_1839_);
return v___x_1844_;
}
default: 
{
v_t_1836_ = v_r_1841_;
goto _start;
}
}
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_box(0);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg___boxed(lean_object* v_t_1847_, lean_object* v_k_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_1847_, v_k_1848_);
lean_dec(v_k_1848_);
lean_dec(v_t_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1850_, lean_object* v_x2_1851_){
_start:
{
lean_object* v_fst_1852_; lean_object* v_fst_1853_; uint8_t v___x_1854_; 
v_fst_1852_ = lean_ctor_get(v_x1_1850_, 0);
v_fst_1853_ = lean_ctor_get(v_x2_1851_, 0);
v___x_1854_ = l_Lean_Name_quickLt(v_fst_1852_, v_fst_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1855_, lean_object* v_x2_1856_){
_start:
{
uint8_t v_res_1857_; lean_object* v_r_1858_; 
v_res_1857_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1855_, v_x2_1856_);
lean_dec_ref(v_x2_1856_);
lean_dec_ref(v_x1_1855_);
v_r_1858_ = lean_box(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1859_, lean_object* v_k_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v_m_1865_; lean_object* v_a_1866_; uint8_t v___x_1867_; 
v___x_1863_ = lean_nat_add(v_x_1861_, v_x_1862_);
v___x_1864_ = lean_unsigned_to_nat(1u);
v_m_1865_ = lean_nat_shiftr(v___x_1863_, v___x_1864_);
lean_dec(v___x_1863_);
v_a_1866_ = lean_array_fget_borrowed(v_as_1859_, v_m_1865_);
v___x_1867_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1866_, v_k_1860_);
if (v___x_1867_ == 0)
{
uint8_t v___x_1868_; 
lean_dec(v_x_1862_);
v___x_1868_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1860_, v_a_1866_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_dec(v_m_1865_);
lean_dec(v_x_1861_);
lean_inc(v_a_1866_);
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1866_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = lean_nat_dec_eq(v_m_1865_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = lean_nat_sub(v_m_1865_, v___x_1864_);
lean_dec(v_m_1865_);
v___x_1873_ = lean_nat_dec_lt(v___x_1872_, v_x_1861_);
if (v___x_1873_ == 0)
{
v_x_1862_ = v___x_1872_;
goto _start;
}
else
{
lean_object* v___x_1875_; 
lean_dec(v___x_1872_);
lean_dec(v_x_1861_);
v___x_1875_ = lean_box(0);
return v___x_1875_;
}
}
else
{
lean_object* v___x_1876_; 
lean_dec(v_m_1865_);
lean_dec(v_x_1861_);
v___x_1876_ = lean_box(0);
return v___x_1876_;
}
}
}
else
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
lean_dec(v_x_1861_);
v___x_1877_ = lean_nat_add(v_m_1865_, v___x_1864_);
lean_dec(v_m_1865_);
v___x_1878_ = lean_nat_dec_le(v___x_1877_, v_x_1862_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_dec(v___x_1877_);
lean_dec(v_x_1862_);
v___x_1879_ = lean_box(0);
return v___x_1879_;
}
else
{
v_x_1861_ = v___x_1877_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1881_, lean_object* v_k_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1881_, v_k_1882_, v_x_1883_, v_x_1884_);
lean_dec_ref(v_k_1882_);
lean_dec_ref(v_as_1881_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v_env_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1890_ = lean_st_ref_get(v___y_1888_);
v_env_1894_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_env_1894_);
lean_dec(v___x_1890_);
v___x_1895_ = lean_box(1);
v___x_1896_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1894_, v_tac_1887_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1897_; lean_object* v_toEnvExtension_1898_; lean_object* v_asyncMode_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1897_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1898_ = lean_ctor_get(v___x_1897_, 0);
v_asyncMode_1899_ = lean_ctor_get(v_toEnvExtension_1898_, 2);
v___x_1900_ = lean_box(0);
v___x_1901_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1895_, v___x_1897_, v_env_1894_, v_asyncMode_1899_, v___x_1900_);
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1901_, v_tac_1887_);
lean_dec(v_tac_1887_);
lean_dec(v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
else
{
lean_object* v_val_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1932_; 
v_val_1904_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1906_ = v___x_1896_;
v_isShared_1907_ = v_isSharedCheck_1932_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_val_1904_);
lean_dec(v___x_1896_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1932_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1908_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1909_ = 0;
v___x_1910_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1895_, v___x_1908_, v_env_1894_, v_val_1904_, v___x_1909_);
lean_dec(v_val_1904_);
lean_dec_ref(v_env_1894_);
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_array_get_size(v___x_1910_);
v___x_1913_ = lean_nat_dec_lt(v___x_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_dec_ref(v___x_1910_);
lean_del_object(v___x_1906_);
lean_dec(v_tac_1887_);
goto v___jp_1891_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_sub(v___x_1912_, v___x_1914_);
v___x_1916_ = lean_nat_dec_le(v___x_1911_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_dec(v___x_1915_);
lean_dec_ref(v___x_1910_);
lean_del_object(v___x_1906_);
lean_dec(v_tac_1887_);
goto v___jp_1891_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_tac_1887_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1910_, v___x_1918_, v___x_1911_, v___x_1915_);
lean_dec_ref(v___x_1918_);
lean_dec_ref(v___x_1910_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_del_object(v___x_1906_);
goto v___jp_1891_;
}
else
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1931_; 
v_val_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1931_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1931_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_snd_1924_; lean_object* v___x_1926_; 
v_snd_1924_ = lean_ctor_get(v_val_1920_, 1);
lean_inc(v_snd_1924_);
lean_dec(v_val_1920_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_snd_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_snd_1924_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1928_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set_tag(v___x_1906_, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1926_);
v___x_1928_ = v___x_1906_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1933_, v___y_1934_);
lean_dec(v___y_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_k_1937_, lean_object* v_v_1938_, lean_object* v_t_1939_){
_start:
{
if (lean_obj_tag(v_t_1939_) == 0)
{
lean_object* v_size_1940_; lean_object* v_k_1941_; lean_object* v_v_1942_; lean_object* v_l_1943_; lean_object* v_r_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2225_; 
v_size_1940_ = lean_ctor_get(v_t_1939_, 0);
v_k_1941_ = lean_ctor_get(v_t_1939_, 1);
v_v_1942_ = lean_ctor_get(v_t_1939_, 2);
v_l_1943_ = lean_ctor_get(v_t_1939_, 3);
v_r_1944_ = lean_ctor_get(v_t_1939_, 4);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_t_1939_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_1946_ = v_t_1939_;
v_isShared_1947_ = v_isSharedCheck_2225_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_r_1944_);
lean_inc(v_l_1943_);
lean_inc(v_v_1942_);
lean_inc(v_k_1941_);
lean_inc(v_size_1940_);
lean_dec(v_t_1939_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2225_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_nat_dec_lt(v_k_1937_, v_k_1941_);
if (v___x_1948_ == 0)
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_nat_dec_eq(v_k_1937_, v_k_1941_);
if (v___x_1949_ == 0)
{
lean_object* v_impl_1950_; lean_object* v___x_1951_; 
lean_dec(v_size_1940_);
v_impl_1950_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1937_, v_v_1938_, v_r_1944_);
v___x_1951_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1943_) == 0)
{
lean_object* v_size_1952_; lean_object* v_size_1953_; lean_object* v_k_1954_; lean_object* v_v_1955_; lean_object* v_l_1956_; lean_object* v_r_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_size_1952_ = lean_ctor_get(v_l_1943_, 0);
v_size_1953_ = lean_ctor_get(v_impl_1950_, 0);
lean_inc(v_size_1953_);
v_k_1954_ = lean_ctor_get(v_impl_1950_, 1);
lean_inc(v_k_1954_);
v_v_1955_ = lean_ctor_get(v_impl_1950_, 2);
lean_inc(v_v_1955_);
v_l_1956_ = lean_ctor_get(v_impl_1950_, 3);
lean_inc(v_l_1956_);
v_r_1957_ = lean_ctor_get(v_impl_1950_, 4);
lean_inc(v_r_1957_);
v___x_1958_ = lean_unsigned_to_nat(3u);
v___x_1959_ = lean_nat_mul(v___x_1958_, v_size_1952_);
v___x_1960_ = lean_nat_dec_lt(v___x_1959_, v_size_1953_);
lean_dec(v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec(v_r_1957_);
lean_dec(v_l_1956_);
lean_dec(v_v_1955_);
lean_dec(v_k_1954_);
v___x_1961_ = lean_nat_add(v___x_1951_, v_size_1952_);
v___x_1962_ = lean_nat_add(v___x_1961_, v_size_1953_);
lean_dec(v_size_1953_);
lean_dec(v___x_1961_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_impl_1950_);
lean_ctor_set(v___x_1946_, 0, v___x_1962_);
v___x_1964_ = v___x_1946_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_1965_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_1965_, 4, v_impl_1950_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2029_; 
v_isSharedCheck_2029_ = !lean_is_exclusive(v_impl_1950_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2030_ = lean_ctor_get(v_impl_1950_, 4);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_impl_1950_, 3);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_impl_1950_, 2);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_impl_1950_, 1);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_impl_1950_, 0);
lean_dec(v_unused_2034_);
v___x_1967_ = v_impl_1950_;
v_isShared_1968_ = v_isSharedCheck_2029_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_impl_1950_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2029_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_size_1969_; lean_object* v_k_1970_; lean_object* v_v_1971_; lean_object* v_l_1972_; lean_object* v_r_1973_; lean_object* v_size_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_size_1969_ = lean_ctor_get(v_l_1956_, 0);
v_k_1970_ = lean_ctor_get(v_l_1956_, 1);
v_v_1971_ = lean_ctor_get(v_l_1956_, 2);
v_l_1972_ = lean_ctor_get(v_l_1956_, 3);
v_r_1973_ = lean_ctor_get(v_l_1956_, 4);
v_size_1974_ = lean_ctor_get(v_r_1957_, 0);
v___x_1975_ = lean_unsigned_to_nat(2u);
v___x_1976_ = lean_nat_mul(v___x_1975_, v_size_1974_);
v___x_1977_ = lean_nat_dec_lt(v_size_1969_, v___x_1976_);
lean_dec(v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2005_; 
lean_inc(v_r_1973_);
lean_inc(v_l_1972_);
lean_inc(v_v_1971_);
lean_inc(v_k_1970_);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_l_1956_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; lean_object* v_unused_2007_; lean_object* v_unused_2008_; lean_object* v_unused_2009_; lean_object* v_unused_2010_; 
v_unused_2006_ = lean_ctor_get(v_l_1956_, 4);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_l_1956_, 3);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_l_1956_, 2);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_l_1956_, 1);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_l_1956_, 0);
lean_dec(v_unused_2010_);
v___x_1979_ = v_l_1956_;
v_isShared_1980_ = v_isSharedCheck_2005_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_l_1956_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2005_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1995_; 
v___x_1981_ = lean_nat_add(v___x_1951_, v_size_1952_);
v___x_1982_ = lean_nat_add(v___x_1981_, v_size_1953_);
lean_dec(v_size_1953_);
if (lean_obj_tag(v_l_1972_) == 0)
{
lean_object* v_size_2003_; 
v_size_2003_ = lean_ctor_get(v_l_1972_, 0);
lean_inc(v_size_2003_);
v___y_1995_ = v_size_2003_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_unsigned_to_nat(0u);
v___y_1995_ = v___x_2004_;
goto v___jp_1994_;
}
v___jp_1983_:
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1987_ = lean_nat_add(v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec(v___y_1985_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v_r_1957_);
lean_ctor_set(v___x_1979_, 3, v_r_1973_);
lean_ctor_set(v___x_1979_, 2, v_v_1955_);
lean_ctor_set(v___x_1979_, 1, v_k_1954_);
lean_ctor_set(v___x_1979_, 0, v___x_1987_);
v___x_1989_ = v___x_1979_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_k_1954_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_v_1955_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_r_1973_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_r_1957_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v___x_1989_);
lean_ctor_set(v___x_1967_, 3, v___y_1984_);
lean_ctor_set(v___x_1967_, 2, v_v_1971_);
lean_ctor_set(v___x_1967_, 1, v_k_1970_);
lean_ctor_set(v___x_1967_, 0, v___x_1982_);
v___x_1991_ = v___x_1967_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v___y_1984_);
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
v___jp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = lean_nat_add(v___x_1981_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec(v___x_1981_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_l_1972_);
lean_ctor_set(v___x_1946_, 0, v___x_1996_);
v___x_1998_ = v___x_1946_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v_l_1972_);
v___x_1998_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_nat_add(v___x_1951_, v_size_1974_);
if (lean_obj_tag(v_r_1973_) == 0)
{
lean_object* v_size_2000_; 
v_size_2000_ = lean_ctor_get(v_r_1973_, 0);
lean_inc(v_size_2000_);
v___y_1984_ = v___x_1998_;
v___y_1985_ = v___x_1999_;
v___y_1986_ = v_size_2000_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_unsigned_to_nat(0u);
v___y_1984_ = v___x_1998_;
v___y_1985_ = v___x_1999_;
v___y_1986_ = v___x_2001_;
goto v___jp_1983_;
}
}
}
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_del_object(v___x_1946_);
v___x_2011_ = lean_nat_add(v___x_1951_, v_size_1952_);
v___x_2012_ = lean_nat_add(v___x_2011_, v_size_1953_);
lean_dec(v_size_1953_);
v___x_2013_ = lean_nat_add(v___x_2011_, v_size_1969_);
lean_dec(v___x_2011_);
lean_inc_ref(v_l_1943_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v_l_1956_);
lean_ctor_set(v___x_1967_, 3, v_l_1943_);
lean_ctor_set(v___x_1967_, 2, v_v_1942_);
lean_ctor_set(v___x_1967_, 1, v_k_1941_);
lean_ctor_set(v___x_1967_, 0, v___x_2013_);
v___x_2015_ = v___x_1967_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_l_1956_);
v___x_2015_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
v_isSharedCheck_2022_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; lean_object* v_unused_2025_; lean_object* v_unused_2026_; lean_object* v_unused_2027_; 
v_unused_2023_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_l_1943_, 2);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_l_1943_, 1);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2027_);
v___x_2017_ = v_l_1943_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_l_1943_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 4, v_r_1957_);
lean_ctor_set(v___x_2017_, 3, v___x_2015_);
lean_ctor_set(v___x_2017_, 2, v_v_1955_);
lean_ctor_set(v___x_2017_, 1, v_k_1954_);
lean_ctor_set(v___x_2017_, 0, v___x_2012_);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_k_1954_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_v_1955_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v_r_1957_);
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
}
}
}
else
{
lean_object* v_l_2035_; 
v_l_2035_ = lean_ctor_get(v_impl_1950_, 3);
lean_inc(v_l_2035_);
if (lean_obj_tag(v_l_2035_) == 0)
{
lean_object* v_r_2036_; lean_object* v_k_2037_; lean_object* v_v_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2061_; 
v_r_2036_ = lean_ctor_get(v_impl_1950_, 4);
v_k_2037_ = lean_ctor_get(v_impl_1950_, 1);
v_v_2038_ = lean_ctor_get(v_impl_1950_, 2);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_impl_1950_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; lean_object* v_unused_2063_; 
v_unused_2062_ = lean_ctor_get(v_impl_1950_, 3);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v_impl_1950_, 0);
lean_dec(v_unused_2063_);
v___x_2040_ = v_impl_1950_;
v_isShared_2041_ = v_isSharedCheck_2061_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_r_2036_);
lean_inc(v_v_2038_);
lean_inc(v_k_2037_);
lean_dec(v_impl_1950_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2061_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_k_2042_; lean_object* v_v_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2057_; 
v_k_2042_ = lean_ctor_get(v_l_2035_, 1);
v_v_2043_ = lean_ctor_get(v_l_2035_, 2);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_l_2035_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; lean_object* v_unused_2059_; lean_object* v_unused_2060_; 
v_unused_2058_ = lean_ctor_get(v_l_2035_, 4);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_l_2035_, 3);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_l_2035_, 0);
lean_dec(v_unused_2060_);
v___x_2045_ = v_l_2035_;
v_isShared_2046_ = v_isSharedCheck_2057_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_v_2043_);
lean_inc(v_k_2042_);
lean_dec(v_l_2035_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2057_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2036_, 2);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 4, v_r_2036_);
lean_ctor_set(v___x_2045_, 3, v_r_2036_);
lean_ctor_set(v___x_2045_, 2, v_v_1942_);
lean_ctor_set(v___x_2045_, 1, v_k_1941_);
lean_ctor_set(v___x_2045_, 0, v___x_1951_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_r_2036_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_r_2036_);
v___x_2049_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
lean_inc(v_r_2036_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 3, v_r_2036_);
lean_ctor_set(v___x_2040_, 0, v___x_1951_);
v___x_2051_ = v___x_2040_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_k_2037_);
lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_v_2038_);
lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_r_2036_);
lean_ctor_set(v_reuseFailAlloc_2055_, 4, v_r_2036_);
v___x_2051_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2053_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2051_);
lean_ctor_set(v___x_1946_, 3, v___x_2049_);
lean_ctor_set(v___x_1946_, 2, v_v_2043_);
lean_ctor_set(v___x_1946_, 1, v_k_2042_);
lean_ctor_set(v___x_1946_, 0, v___x_2047_);
v___x_2053_ = v___x_1946_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_k_2042_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_v_2043_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
}
else
{
lean_object* v_r_2064_; 
v_r_2064_ = lean_ctor_get(v_impl_1950_, 4);
lean_inc(v_r_2064_);
if (lean_obj_tag(v_r_2064_) == 0)
{
lean_object* v_k_2065_; lean_object* v_v_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2077_; 
v_k_2065_ = lean_ctor_get(v_impl_1950_, 1);
v_v_2066_ = lean_ctor_get(v_impl_1950_, 2);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_impl_1950_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; lean_object* v_unused_2079_; lean_object* v_unused_2080_; 
v_unused_2078_ = lean_ctor_get(v_impl_1950_, 4);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_impl_1950_, 3);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v_impl_1950_, 0);
lean_dec(v_unused_2080_);
v___x_2068_ = v_impl_1950_;
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_v_2066_);
lean_inc(v_k_2065_);
lean_dec(v_impl_1950_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_unsigned_to_nat(3u);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_l_2035_);
lean_ctor_set(v___x_2068_, 2, v_v_1942_);
lean_ctor_set(v___x_2068_, 1, v_k_1941_);
lean_ctor_set(v___x_2068_, 0, v___x_1951_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_l_2035_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_r_2064_);
lean_ctor_set(v___x_1946_, 3, v___x_2072_);
lean_ctor_set(v___x_1946_, 2, v_v_2066_);
lean_ctor_set(v___x_1946_, 1, v_k_2065_);
lean_ctor_set(v___x_1946_, 0, v___x_2070_);
v___x_2074_ = v___x_1946_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_r_2064_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_unsigned_to_nat(2u);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_impl_1950_);
lean_ctor_set(v___x_1946_, 3, v_r_2064_);
lean_ctor_set(v___x_1946_, 0, v___x_2081_);
v___x_2083_ = v___x_1946_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_r_2064_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_impl_1950_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v___x_2086_; 
lean_dec(v_v_1942_);
lean_dec(v_k_1941_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 2, v_v_1938_);
lean_ctor_set(v___x_1946_, 1, v_k_1937_);
v___x_2086_ = v___x_1946_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_size_1940_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_r_1944_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
lean_object* v_impl_2088_; lean_object* v___x_2089_; 
lean_dec(v_size_1940_);
v_impl_2088_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1937_, v_v_1938_, v_l_1943_);
v___x_2089_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1944_) == 0)
{
lean_object* v_size_2090_; lean_object* v_size_2091_; lean_object* v_k_2092_; lean_object* v_v_2093_; lean_object* v_l_2094_; lean_object* v_r_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_size_2090_ = lean_ctor_get(v_r_1944_, 0);
v_size_2091_ = lean_ctor_get(v_impl_2088_, 0);
lean_inc(v_size_2091_);
v_k_2092_ = lean_ctor_get(v_impl_2088_, 1);
lean_inc(v_k_2092_);
v_v_2093_ = lean_ctor_get(v_impl_2088_, 2);
lean_inc(v_v_2093_);
v_l_2094_ = lean_ctor_get(v_impl_2088_, 3);
lean_inc(v_l_2094_);
v_r_2095_ = lean_ctor_get(v_impl_2088_, 4);
lean_inc(v_r_2095_);
v___x_2096_ = lean_unsigned_to_nat(3u);
v___x_2097_ = lean_nat_mul(v___x_2096_, v_size_2090_);
v___x_2098_ = lean_nat_dec_lt(v___x_2097_, v_size_2091_);
lean_dec(v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec(v_r_2095_);
lean_dec(v_l_2094_);
lean_dec(v_v_2093_);
lean_dec(v_k_2092_);
v___x_2099_ = lean_nat_add(v___x_2089_, v_size_2091_);
lean_dec(v_size_2091_);
v___x_2100_ = lean_nat_add(v___x_2099_, v_size_2090_);
lean_dec(v___x_2099_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 3, v_impl_2088_);
lean_ctor_set(v___x_1946_, 0, v___x_2100_);
v___x_2102_ = v___x_1946_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_impl_2088_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_r_1944_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2169_; 
v_isSharedCheck_2169_ = !lean_is_exclusive(v_impl_2088_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; lean_object* v_unused_2171_; lean_object* v_unused_2172_; lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2170_ = lean_ctor_get(v_impl_2088_, 4);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_impl_2088_, 3);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_impl_2088_, 2);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_impl_2088_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_impl_2088_, 0);
lean_dec(v_unused_2174_);
v___x_2105_ = v_impl_2088_;
v_isShared_2106_ = v_isSharedCheck_2169_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v_impl_2088_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2169_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_size_2107_; lean_object* v_size_2108_; lean_object* v_k_2109_; lean_object* v_v_2110_; lean_object* v_l_2111_; lean_object* v_r_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_size_2107_ = lean_ctor_get(v_l_2094_, 0);
v_size_2108_ = lean_ctor_get(v_r_2095_, 0);
v_k_2109_ = lean_ctor_get(v_r_2095_, 1);
v_v_2110_ = lean_ctor_get(v_r_2095_, 2);
v_l_2111_ = lean_ctor_get(v_r_2095_, 3);
v_r_2112_ = lean_ctor_get(v_r_2095_, 4);
v___x_2113_ = lean_unsigned_to_nat(2u);
v___x_2114_ = lean_nat_mul(v___x_2113_, v_size_2107_);
v___x_2115_ = lean_nat_dec_lt(v_size_2108_, v___x_2114_);
lean_dec(v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2144_; 
lean_inc(v_r_2112_);
lean_inc(v_l_2111_);
lean_inc(v_v_2110_);
lean_inc(v_k_2109_);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_r_2095_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; 
v_unused_2145_ = lean_ctor_get(v_r_2095_, 4);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_r_2095_, 3);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_r_2095_, 2);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_r_2095_, 1);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_r_2095_, 0);
lean_dec(v_unused_2149_);
v___x_2117_ = v_r_2095_;
v_isShared_2118_ = v_isSharedCheck_2144_;
goto v_resetjp_2116_;
}
else
{
lean_dec(v_r_2095_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2144_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___x_2132_; lean_object* v___y_2134_; 
v___x_2119_ = lean_nat_add(v___x_2089_, v_size_2091_);
lean_dec(v_size_2091_);
v___x_2120_ = lean_nat_add(v___x_2119_, v_size_2090_);
lean_dec(v___x_2119_);
v___x_2132_ = lean_nat_add(v___x_2089_, v_size_2107_);
if (lean_obj_tag(v_l_2111_) == 0)
{
lean_object* v_size_2142_; 
v_size_2142_ = lean_ctor_get(v_l_2111_, 0);
lean_inc(v_size_2142_);
v___y_2134_ = v_size_2142_;
goto v___jp_2133_;
}
else
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_unsigned_to_nat(0u);
v___y_2134_ = v___x_2143_;
goto v___jp_2133_;
}
v___jp_2121_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = lean_nat_add(v___y_2122_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec(v___y_2122_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 4, v_r_1944_);
lean_ctor_set(v___x_2117_, 3, v_r_2112_);
lean_ctor_set(v___x_2117_, 2, v_v_1942_);
lean_ctor_set(v___x_2117_, 1, v_k_1941_);
lean_ctor_set(v___x_2117_, 0, v___x_2125_);
v___x_2127_ = v___x_2117_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_r_2112_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v_r_1944_);
v___x_2127_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2129_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 4, v___x_2127_);
lean_ctor_set(v___x_2105_, 3, v___y_2123_);
lean_ctor_set(v___x_2105_, 2, v_v_2110_);
lean_ctor_set(v___x_2105_, 1, v_k_2109_);
lean_ctor_set(v___x_2105_, 0, v___x_2120_);
v___x_2129_ = v___x_2105_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_k_2109_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_v_2110_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v___y_2123_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
v___jp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_nat_add(v___x_2132_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec(v___x_2132_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_l_2111_);
lean_ctor_set(v___x_1946_, 3, v_l_2094_);
lean_ctor_set(v___x_1946_, 2, v_v_2093_);
lean_ctor_set(v___x_1946_, 1, v_k_2092_);
lean_ctor_set(v___x_1946_, 0, v___x_2135_);
v___x_2137_ = v___x_1946_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_l_2094_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_l_2111_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_nat_add(v___x_2089_, v_size_2090_);
if (lean_obj_tag(v_r_2112_) == 0)
{
lean_object* v_size_2139_; 
v_size_2139_ = lean_ctor_get(v_r_2112_, 0);
lean_inc(v_size_2139_);
v___y_2122_ = v___x_2138_;
v___y_2123_ = v___x_2137_;
v___y_2124_ = v_size_2139_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2140_; 
v___x_2140_ = lean_unsigned_to_nat(0u);
v___y_2122_ = v___x_2138_;
v___y_2123_ = v___x_2137_;
v___y_2124_ = v___x_2140_;
goto v___jp_2121_;
}
}
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
lean_del_object(v___x_1946_);
v___x_2150_ = lean_nat_add(v___x_2089_, v_size_2091_);
lean_dec(v_size_2091_);
v___x_2151_ = lean_nat_add(v___x_2150_, v_size_2090_);
lean_dec(v___x_2150_);
v___x_2152_ = lean_nat_add(v___x_2089_, v_size_2090_);
v___x_2153_ = lean_nat_add(v___x_2152_, v_size_2108_);
lean_dec(v___x_2152_);
lean_inc_ref(v_r_1944_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 4, v_r_1944_);
lean_ctor_set(v___x_2105_, 3, v_r_2095_);
lean_ctor_set(v___x_2105_, 2, v_v_1942_);
lean_ctor_set(v___x_2105_, 1, v_k_1941_);
lean_ctor_set(v___x_2105_, 0, v___x_2153_);
v___x_2155_ = v___x_2105_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v_r_2095_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v_r_1944_);
v___x_2155_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
v_isSharedCheck_2162_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; lean_object* v_unused_2166_; lean_object* v_unused_2167_; 
v_unused_2163_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_r_1944_, 2);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_r_1944_, 1);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_r_1944_, 0);
lean_dec(v_unused_2167_);
v___x_2157_ = v_r_1944_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_dec(v_r_1944_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 4, v___x_2155_);
lean_ctor_set(v___x_2157_, 3, v_l_2094_);
lean_ctor_set(v___x_2157_, 2, v_v_2093_);
lean_ctor_set(v___x_2157_, 1, v_k_2092_);
lean_ctor_set(v___x_2157_, 0, v___x_2151_);
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_k_2092_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_v_2093_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_l_2094_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v___x_2155_);
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
}
}
}
else
{
lean_object* v_l_2175_; 
v_l_2175_ = lean_ctor_get(v_impl_2088_, 3);
lean_inc(v_l_2175_);
if (lean_obj_tag(v_l_2175_) == 0)
{
lean_object* v_r_2176_; lean_object* v_k_2177_; lean_object* v_v_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2189_; 
v_r_2176_ = lean_ctor_get(v_impl_2088_, 4);
v_k_2177_ = lean_ctor_get(v_impl_2088_, 1);
v_v_2178_ = lean_ctor_get(v_impl_2088_, 2);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_impl_2088_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2190_ = lean_ctor_get(v_impl_2088_, 3);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_impl_2088_, 0);
lean_dec(v_unused_2191_);
v___x_2180_ = v_impl_2088_;
v_isShared_2181_ = v_isSharedCheck_2189_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_r_2176_);
lean_inc(v_v_2178_);
lean_inc(v_k_2177_);
lean_dec(v_impl_2088_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2189_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2176_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 3, v_r_2176_);
lean_ctor_set(v___x_2180_, 2, v_v_1942_);
lean_ctor_set(v___x_2180_, 1, v_k_1941_);
lean_ctor_set(v___x_2180_, 0, v___x_2089_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_r_2176_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_r_2176_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2184_);
lean_ctor_set(v___x_1946_, 3, v_l_2175_);
lean_ctor_set(v___x_1946_, 2, v_v_2178_);
lean_ctor_set(v___x_1946_, 1, v_k_2177_);
lean_ctor_set(v___x_1946_, 0, v___x_2182_);
v___x_2186_ = v___x_1946_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_2177_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_2178_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_l_2175_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_r_2192_; 
v_r_2192_ = lean_ctor_get(v_impl_2088_, 4);
lean_inc(v_r_2192_);
if (lean_obj_tag(v_r_2192_) == 0)
{
lean_object* v_k_2193_; lean_object* v_v_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2217_; 
v_k_2193_ = lean_ctor_get(v_impl_2088_, 1);
v_v_2194_ = lean_ctor_get(v_impl_2088_, 2);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_impl_2088_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; lean_object* v_unused_2219_; lean_object* v_unused_2220_; 
v_unused_2218_ = lean_ctor_get(v_impl_2088_, 4);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_impl_2088_, 3);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_impl_2088_, 0);
lean_dec(v_unused_2220_);
v___x_2196_ = v_impl_2088_;
v_isShared_2197_ = v_isSharedCheck_2217_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_v_2194_);
lean_inc(v_k_2193_);
lean_dec(v_impl_2088_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2217_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v_k_2198_; lean_object* v_v_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2213_; 
v_k_2198_ = lean_ctor_get(v_r_2192_, 1);
v_v_2199_ = lean_ctor_get(v_r_2192_, 2);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_r_2192_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; lean_object* v_unused_2215_; lean_object* v_unused_2216_; 
v_unused_2214_ = lean_ctor_get(v_r_2192_, 4);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_r_2192_, 3);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_r_2192_, 0);
lean_dec(v_unused_2216_);
v___x_2201_ = v_r_2192_;
v_isShared_2202_ = v_isSharedCheck_2213_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_v_2199_);
lean_inc(v_k_2198_);
lean_dec(v_r_2192_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2213_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_unsigned_to_nat(3u);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_l_2175_);
lean_ctor_set(v___x_2201_, 3, v_l_2175_);
lean_ctor_set(v___x_2201_, 2, v_v_2194_);
lean_ctor_set(v___x_2201_, 1, v_k_2193_);
lean_ctor_set(v___x_2201_, 0, v___x_2089_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_k_2193_);
lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_v_2194_);
lean_ctor_set(v_reuseFailAlloc_2212_, 3, v_l_2175_);
lean_ctor_set(v_reuseFailAlloc_2212_, 4, v_l_2175_);
v___x_2205_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2207_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v_l_2175_);
lean_ctor_set(v___x_2196_, 2, v_v_1942_);
lean_ctor_set(v___x_2196_, 1, v_k_1941_);
lean_ctor_set(v___x_2196_, 0, v___x_2089_);
v___x_2207_ = v___x_2196_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_l_2175_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_l_2175_);
v___x_2207_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2209_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2207_);
lean_ctor_set(v___x_1946_, 3, v___x_2205_);
lean_ctor_set(v___x_1946_, 2, v_v_2199_);
lean_ctor_set(v___x_1946_, 1, v_k_2198_);
lean_ctor_set(v___x_1946_, 0, v___x_2203_);
v___x_2209_ = v___x_1946_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2198_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2199_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v___x_2207_);
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
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2221_ = lean_unsigned_to_nat(2u);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_r_2192_);
lean_ctor_set(v___x_1946_, 3, v_impl_2088_);
lean_ctor_set(v___x_1946_, 0, v___x_2221_);
v___x_2223_ = v___x_1946_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_impl_2088_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_r_2192_);
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
}
}
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v_k_1937_);
lean_ctor_set(v___x_2227_, 2, v_v_1938_);
lean_ctor_set(v___x_2227_, 3, v_t_1939_);
lean_ctor_set(v___x_2227_, 4, v_t_1939_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_as_x27_2228_, lean_object* v_b_2229_){
_start:
{
if (lean_obj_tag(v_as_x27_2228_) == 0)
{
return v_b_2229_;
}
else
{
lean_object* v_head_2230_; lean_object* v_tail_2231_; lean_object* v_fst_2232_; lean_object* v_snd_2233_; lean_object* v_r_2234_; 
v_head_2230_ = lean_ctor_get(v_as_x27_2228_, 0);
v_tail_2231_ = lean_ctor_get(v_as_x27_2228_, 1);
v_fst_2232_ = lean_ctor_get(v_head_2230_, 0);
v_snd_2233_ = lean_ctor_get(v_head_2230_, 1);
lean_inc(v_snd_2233_);
lean_inc(v_fst_2232_);
v_r_2234_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_fst_2232_, v_snd_2233_, v_b_2229_);
v_as_x27_2228_ = v_tail_2231_;
v_b_2229_ = v_r_2234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_as_x27_2236_, lean_object* v_b_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_as_x27_2236_, v_b_2237_);
lean_dec(v_as_x27_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_2239_, lean_object* v_n_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2277_; lean_object* v_val_2278_; lean_object* v___x_2280_; lean_object* v___y_2282_; lean_object* v_env_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2280_ = lean_st_ref_get(v___y_2242_);
v_env_2297_ = lean_ctor_get(v___x_2280_, 0);
lean_inc_ref(v_env_2297_);
lean_dec(v___x_2280_);
v___x_2298_ = l_Lean_Environment_constants(v_env_2297_);
v___x_2299_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v___x_2298_, v_n_2240_);
lean_dec_ref(v___x_2298_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_box(0);
v___y_2282_ = v___x_2300_;
goto v___jp_2281_;
}
else
{
lean_object* v_val_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_val_2301_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_val_2301_);
lean_dec_ref(v___x_2299_);
v___x_2302_ = l_Lean_ConstantInfo_levelParams(v_val_2301_);
lean_dec(v_val_2301_);
v___x_2303_ = lean_box(0);
v___x_2304_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(v___x_2302_, v___x_2303_);
v___y_2282_ = v___x_2304_;
goto v___jp_2281_;
}
v___jp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_r_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___y_2246_);
v___x_2250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2247_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v___x_2247_);
v___x_2252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_2253_ = lean_box(2);
v___x_2254_ = 1;
lean_inc_n(v_n_2240_, 3);
v___x_2255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_2240_, v___x_2254_);
v___x_2256_ = lean_string_utf8_byte_size(v___x_2255_);
v___x_2257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2248_);
lean_ctor_set(v___x_2257_, 2, v___x_2256_);
v___x_2258_ = lean_box(0);
v___x_2259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_n_2240_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
lean_ctor_set(v___x_2260_, 1, v___x_2258_);
v___x_2261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2253_);
lean_ctor_set(v___x_2261_, 1, v___x_2257_);
lean_ctor_set(v___x_2261_, 2, v_n_2240_);
lean_ctor_set(v___x_2261_, 3, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2252_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_LocalContext_empty;
v___x_2264_ = lean_box(0);
v___x_2265_ = l_Lean_Expr_const___override(v_n_2240_, v___y_2245_);
v___x_2266_ = 0;
v___x_2267_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2267_, 0, v___x_2262_);
lean_ctor_set(v___x_2267_, 1, v___x_2263_);
lean_ctor_set(v___x_2267_, 2, v___x_2264_);
lean_ctor_set(v___x_2267_, 3, v___x_2265_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*4, v___x_2266_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*4 + 1, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2248_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___x_2258_);
v_r_2271_ = lean_box(1);
v___x_2272_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_2270_, v_r_2271_);
lean_dec_ref(v___x_2270_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2251_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
return v___x_2275_;
}
v___jp_2276_:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_val_2278_);
v___y_2245_ = v___y_2277_;
v___y_2246_ = v___x_2279_;
goto v___jp_2244_;
}
v___jp_2281_:
{
lean_object* v___x_2283_; lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2296_; 
lean_inc(v_n_2240_);
v___x_2283_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_2240_, v___y_2242_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2296_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2296_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
if (lean_obj_tag(v_a_2284_) == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_firsts_2239_, v_n_2240_);
if (lean_obj_tag(v___x_2288_) == 0)
{
uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2289_ = 1;
lean_inc(v_n_2240_);
v___x_2290_ = l_Lean_Name_toString(v_n_2240_, v___x_2289_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 3);
lean_ctor_set(v___x_2286_, 0, v___x_2290_);
v___x_2292_ = v___x_2286_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
v___y_2245_ = v___y_2282_;
v___y_2246_ = v___x_2292_;
goto v___jp_2244_;
}
}
else
{
lean_object* v_val_2294_; 
lean_del_object(v___x_2286_);
v_val_2294_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_val_2294_);
lean_dec_ref(v___x_2288_);
v___y_2277_ = v___y_2282_;
v_val_2278_ = v_val_2294_;
goto v___jp_2276_;
}
}
else
{
lean_object* v_val_2295_; 
lean_del_object(v___x_2286_);
v_val_2295_ = lean_ctor_get(v_a_2284_, 0);
lean_inc(v_val_2295_);
lean_dec_ref(v_a_2284_);
v___y_2277_ = v___y_2282_;
v_val_2278_ = v_val_2295_;
goto v___jp_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_2305_, lean_object* v_n_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_2305_, v_n_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v_firsts_2305_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
if (lean_obj_tag(v_x_2312_) == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = l_List_reverse___redArg(v_x_2313_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
else
{
lean_object* v_head_2319_; lean_object* v_tail_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2338_; 
v_head_2319_ = lean_ctor_get(v_x_2312_, 0);
v_tail_2320_ = lean_ctor_get(v_x_2312_, 1);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_x_2312_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2322_ = v_x_2312_;
v_isShared_2323_ = v_isSharedCheck_2338_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_tail_2320_);
lean_inc(v_head_2319_);
lean_dec(v_x_2312_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2338_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; 
v___x_2324_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_2311_, v_head_2319_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v___x_2324_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v_x_2313_);
lean_ctor_set(v___x_2322_, 0, v_a_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2325_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_x_2313_);
v___x_2327_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
v_x_2312_ = v_tail_2320_;
v_x_2313_ = v___x_2327_;
goto _start;
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_del_object(v___x_2322_);
lean_dec(v_tail_2320_);
lean_dec(v_x_2313_);
v_a_2330_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2324_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2324_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2339_, v_x_2340_, v_x_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v_a_2339_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_2346_, lean_object* v___x_2347_, lean_object* v___x_2348_, lean_object* v_a_2349_, lean_object* v_b_2350_){
_start:
{
lean_object* v_it_2352_; lean_object* v_startInclusive_2353_; lean_object* v_endExclusive_2354_; 
if (lean_obj_tag(v_a_2349_) == 0)
{
lean_object* v_currPos_2359_; lean_object* v_searcher_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2386_; 
v_currPos_2359_ = lean_ctor_get(v_a_2349_, 0);
v_searcher_2360_ = lean_ctor_get(v_a_2349_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_a_2349_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2362_ = v_a_2349_;
v_isShared_2363_ = v_isSharedCheck_2386_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_searcher_2360_);
lean_inc(v_currPos_2359_);
lean_dec(v_a_2349_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2386_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_startInclusive_2364_; lean_object* v_endExclusive_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_startInclusive_2364_ = lean_ctor_get(v___x_2347_, 1);
v_endExclusive_2365_ = lean_ctor_get(v___x_2347_, 2);
v___x_2366_ = lean_nat_sub(v_endExclusive_2365_, v_startInclusive_2364_);
v___x_2367_ = lean_nat_dec_eq(v_searcher_2360_, v___x_2366_);
lean_dec(v___x_2366_);
if (v___x_2367_ == 0)
{
uint32_t v___x_2368_; uint32_t v___x_2369_; uint8_t v___x_2370_; 
v___x_2368_ = 10;
v___x_2369_ = lean_string_utf8_get_fast(v_val_2346_, v_searcher_2360_);
v___x_2370_ = lean_uint32_dec_eq(v___x_2369_, v___x_2368_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = lean_string_utf8_next_fast(v_val_2346_, v_searcher_2360_);
lean_dec(v_searcher_2360_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2371_);
v___x_2373_ = v___x_2362_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_currPos_2359_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
v_a_2349_ = v___x_2373_;
goto _start;
}
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_slice_2379_; lean_object* v_nextIt_2381_; 
v___x_2376_ = lean_string_utf8_next_fast(v_val_2346_, v_searcher_2360_);
v___x_2377_ = lean_nat_sub(v___x_2376_, v_searcher_2360_);
v___x_2378_ = lean_nat_add(v_searcher_2360_, v___x_2377_);
lean_dec(v___x_2377_);
v_slice_2379_ = l_String_Slice_subslice_x21(v___x_2347_, v_currPos_2359_, v_searcher_2360_);
lean_inc(v___x_2378_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2378_);
lean_ctor_set(v___x_2362_, 0, v___x_2378_);
v_nextIt_2381_ = v___x_2362_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2378_);
v_nextIt_2381_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v_startInclusive_2382_; lean_object* v_endExclusive_2383_; 
v_startInclusive_2382_ = lean_ctor_get(v_slice_2379_, 0);
lean_inc(v_startInclusive_2382_);
v_endExclusive_2383_ = lean_ctor_get(v_slice_2379_, 1);
lean_inc(v_endExclusive_2383_);
lean_dec_ref(v_slice_2379_);
v_it_2352_ = v_nextIt_2381_;
v_startInclusive_2353_ = v_startInclusive_2382_;
v_endExclusive_2354_ = v_endExclusive_2383_;
goto v___jp_2351_;
}
}
}
else
{
lean_object* v___x_2385_; 
lean_del_object(v___x_2362_);
lean_dec(v_searcher_2360_);
v___x_2385_ = lean_box(1);
lean_inc(v___x_2348_);
v_it_2352_ = v___x_2385_;
v_startInclusive_2353_ = v_currPos_2359_;
v_endExclusive_2354_ = v___x_2348_;
goto v___jp_2351_;
}
}
}
else
{
lean_dec(v___x_2348_);
return v_b_2350_;
}
v___jp_2351_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_string_utf8_extract(v_val_2346_, v_startInclusive_2353_, v_endExclusive_2354_);
lean_dec(v_endExclusive_2354_);
lean_dec(v_startInclusive_2353_);
v___x_2356_ = l_Lean_stringToMessageData(v___x_2355_);
v___x_2357_ = lean_array_push(v_b_2350_, v___x_2356_);
v_a_2349_ = v_it_2352_;
v_b_2350_ = v___x_2357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2387_, lean_object* v___x_2388_, lean_object* v___x_2389_, lean_object* v_a_2390_, lean_object* v_b_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2387_, v___x_2388_, v___x_2389_, v_a_2390_, v_b_2391_);
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_val_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(lean_object* v_init_2393_, lean_object* v_x_2394_){
_start:
{
if (lean_obj_tag(v_x_2394_) == 0)
{
lean_object* v_k_2395_; lean_object* v_l_2396_; lean_object* v_r_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_k_2395_ = lean_ctor_get(v_x_2394_, 1);
lean_inc(v_k_2395_);
v_l_2396_ = lean_ctor_get(v_x_2394_, 3);
lean_inc(v_l_2396_);
v_r_2397_ = lean_ctor_get(v_x_2394_, 4);
lean_inc(v_r_2397_);
lean_dec_ref(v_x_2394_);
v___x_2398_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_2393_, v_l_2396_);
v___x_2399_ = lean_array_push(v___x_2398_, v_k_2395_);
v_init_2393_ = v___x_2399_;
v_x_2394_ = v_r_2397_;
goto _start;
}
else
{
return v_init_2393_;
}
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2405_ = l_Lean_stringToMessageData(v___x_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2408_ = l_Lean_stringToMessageData(v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2416_ = l_Lean_MessageData_ofFormat(v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_x_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
if (lean_obj_tag(v_x_2419_) == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = l_List_reverse___redArg(v_x_2420_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
else
{
lean_object* v_head_2426_; lean_object* v_tail_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2524_; 
v_head_2426_ = lean_ctor_get(v_x_2419_, 0);
v_tail_2427_ = lean_ctor_get(v_x_2419_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_x_2419_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2429_ = v_x_2419_;
v_isShared_2430_ = v_isSharedCheck_2524_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_tail_2427_);
lean_inc(v_head_2426_);
lean_dec(v_x_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2524_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v_snd_2444_; lean_object* v_fst_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2523_; 
v_snd_2444_ = lean_ctor_get(v_head_2426_, 1);
v_fst_2445_ = lean_ctor_get(v_head_2426_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_head_2426_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2447_ = v_head_2426_;
v_isShared_2448_ = v_isSharedCheck_2523_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_snd_2444_);
lean_inc(v_fst_2445_);
lean_dec(v_head_2426_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2523_;
goto v_resetjp_2446_;
}
v___jp_2431_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___y_2433_);
lean_ctor_set(v___x_2436_, 1, v___y_2435_);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v___y_2434_);
v___x_2438_ = l_Lean_MessageData_nestD(v___x_2437_);
lean_inc_ref(v___y_2432_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___y_2432_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 1, v_x_2420_);
lean_ctor_set(v___x_2429_, 0, v___x_2439_);
v___x_2441_ = v___x_2429_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_x_2420_);
v___x_2441_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
v_x_2419_ = v_tail_2427_;
v_x_2420_ = v___x_2441_;
goto _start;
}
}
v_resetjp_2446_:
{
lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2522_; 
v_fst_2449_ = lean_ctor_get(v_snd_2444_, 0);
v_snd_2450_ = lean_ctor_get(v_snd_2444_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_snd_2444_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2452_ = v_snd_2444_;
v_isShared_2453_ = v_isSharedCheck_2522_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snd_2450_);
lean_inc(v_fst_2449_);
lean_dec(v_snd_2444_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2522_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_a_2477_; lean_object* v___y_2493_; lean_object* v___x_2502_; 
v___x_2502_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2418_, v_fst_2445_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_MessageData_nil;
v_a_2477_ = v___x_2503_;
goto v___jp_2476_;
}
else
{
lean_object* v_val_2504_; 
v_val_2504_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_val_2504_);
lean_dec_ref(v___x_2502_);
if (lean_obj_tag(v_val_2504_) == 0)
{
lean_object* v_size_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v_size_2505_ = lean_ctor_get(v_val_2504_, 0);
v___x_2506_ = lean_mk_empty_array_with_capacity(v_size_2505_);
v___x_2507_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v___x_2506_, v_val_2504_);
v___x_2508_ = lean_array_get_size(v___x_2507_);
v___x_2513_ = lean_unsigned_to_nat(0u);
v___x_2514_ = lean_nat_dec_eq(v___x_2508_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___y_2518_; uint8_t v___x_2520_; 
v___x_2515_ = lean_unsigned_to_nat(1u);
v___x_2516_ = lean_nat_sub(v___x_2508_, v___x_2515_);
v___x_2520_ = lean_nat_dec_le(v___x_2513_, v___x_2516_);
if (v___x_2520_ == 0)
{
lean_inc(v___x_2516_);
v___y_2518_ = v___x_2516_;
goto v___jp_2517_;
}
else
{
v___y_2518_ = v___x_2513_;
goto v___jp_2517_;
}
v___jp_2517_:
{
uint8_t v___x_2519_; 
v___x_2519_ = lean_nat_dec_le(v___y_2518_, v___x_2516_);
if (v___x_2519_ == 0)
{
lean_dec(v___x_2516_);
lean_inc(v___y_2518_);
v___y_2510_ = v___y_2518_;
v___y_2511_ = v___y_2518_;
goto v___jp_2509_;
}
else
{
v___y_2510_ = v___y_2518_;
v___y_2511_ = v___x_2516_;
goto v___jp_2509_;
}
}
}
else
{
v___y_2493_ = v___x_2507_;
goto v___jp_2492_;
}
v___jp_2509_:
{
lean_object* v___x_2512_; 
v___x_2512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2508_, v___x_2507_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
v___y_2493_ = v___x_2512_;
goto v___jp_2492_;
}
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_MessageData_nil;
v_a_2477_ = v___x_2521_;
goto v___jp_2476_;
}
}
v___jp_2454_:
{
lean_object* v___x_2460_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set_tag(v___x_2452_, 7);
lean_ctor_set(v___x_2452_, 1, v___y_2458_);
lean_ctor_set(v___x_2452_, 0, v___y_2456_);
v___x_2460_ = v___x_2452_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___y_2456_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___y_2458_);
v___x_2460_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
if (lean_obj_tag(v_snd_2450_) == 0)
{
lean_object* v___x_2461_; 
lean_del_object(v___x_2447_);
v___x_2461_ = l_Lean_MessageData_nil;
v___y_2432_ = v___y_2455_;
v___y_2433_ = v___x_2460_;
v___y_2434_ = v___y_2457_;
v___y_2435_ = v___x_2461_;
goto v___jp_2431_;
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v_val_2462_ = lean_ctor_get(v_snd_2450_, 0);
lean_inc_n(v_val_2462_, 2);
lean_dec_ref(v_snd_2450_);
v___x_2463_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_string_utf8_byte_size(v_val_2462_);
v___x_2466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2466_, 0, v_val_2462_);
lean_ctor_set(v___x_2466_, 1, v___x_2464_);
lean_ctor_set(v___x_2466_, 2, v___x_2465_);
v___x_2467_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2466_);
v___x_2468_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2469_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2462_, v___x_2466_, v___x_2465_, v___x_2467_, v___x_2468_);
lean_dec_ref(v___x_2466_);
lean_dec(v_val_2462_);
v___x_2470_ = lean_array_to_list(v___x_2469_);
v___x_2471_ = l_Lean_MessageData_joinSep(v___x_2470_, v___x_2463_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set_tag(v___x_2447_, 7);
lean_ctor_set(v___x_2447_, 1, v___x_2471_);
lean_ctor_set(v___x_2447_, 0, v___x_2463_);
v___x_2473_ = v___x_2447_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
v___y_2432_ = v___y_2455_;
v___y_2433_ = v___x_2460_;
v___y_2434_ = v___y_2457_;
v___y_2435_ = v___x_2473_;
goto v___jp_2431_;
}
}
}
}
v___jp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2478_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2479_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2445_);
v___x_2480_ = l_Lean_MessageData_ofName(v_fst_2445_);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v___x_2479_);
v___x_2483_ = 1;
v___x_2484_ = l_Lean_Name_toString(v_fst_2445_, v___x_2483_);
v___x_2485_ = lean_string_dec_eq(v___x_2484_, v_fst_2449_);
lean_dec_ref(v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2486_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2487_ = l_Lean_stringToMessageData(v_fst_2449_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___y_2455_ = v___x_2478_;
v___y_2456_ = v___x_2482_;
v___y_2457_ = v_a_2477_;
v___y_2458_ = v___x_2490_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2491_; 
lean_dec(v_fst_2449_);
v___x_2491_ = l_Lean_MessageData_nil;
v___y_2455_ = v___x_2478_;
v___y_2456_ = v___x_2482_;
v___y_2457_ = v_a_2477_;
v___y_2458_ = v___x_2491_;
goto v___jp_2454_;
}
}
v___jp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_array_to_list(v___y_2493_);
v___x_2495_ = lean_box(0);
v___x_2496_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2417_, v___x_2494_, v___x_2495_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2499_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2500_ = l_Lean_MessageData_joinSep(v_a_2497_, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2498_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v_a_2477_ = v___x_2501_;
goto v___jp_2476_;
}
else
{
lean_del_object(v___x_2452_);
lean_dec(v_snd_2450_);
lean_dec(v_fst_2449_);
lean_del_object(v___x_2447_);
lean_dec(v_fst_2445_);
lean_del_object(v___x_2429_);
lean_dec(v_tail_2427_);
lean_dec(v_x_2420_);
return v___x_2496_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_x_2527_, lean_object* v_x_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2525_, v_a_2526_, v_x_2527_, v_x_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v_a_2526_);
lean_dec(v_a_2525_);
return v_res_2532_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0(uint8_t v___y_2534_, uint8_t v_suppressElabErrors_2535_, lean_object* v_x_2536_){
_start:
{
if (lean_obj_tag(v_x_2536_) == 1)
{
lean_object* v_pre_2537_; 
v_pre_2537_ = lean_ctor_get(v_x_2536_, 0);
if (lean_obj_tag(v_pre_2537_) == 0)
{
lean_object* v_str_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_str_2538_ = lean_ctor_get(v_x_2536_, 1);
v___x_2539_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0));
v___x_2540_ = lean_string_dec_eq(v_str_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
return v___y_2534_;
}
else
{
return v_suppressElabErrors_2535_;
}
}
else
{
return v___y_2534_;
}
}
else
{
return v___y_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___boxed(lean_object* v___y_2541_, lean_object* v_suppressElabErrors_2542_, lean_object* v_x_2543_){
_start:
{
uint8_t v___y_19941__boxed_2544_; uint8_t v_suppressElabErrors_boxed_2545_; uint8_t v_res_2546_; lean_object* v_r_2547_; 
v___y_19941__boxed_2544_ = lean_unbox(v___y_2541_);
v_suppressElabErrors_boxed_2545_ = lean_unbox(v_suppressElabErrors_2542_);
v_res_2546_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0(v___y_19941__boxed_2544_, v_suppressElabErrors_boxed_2545_, v_x_2543_);
lean_dec(v_x_2543_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(lean_object* v_ref_2548_, lean_object* v_msgData_2549_, uint8_t v_severity_2550_, uint8_t v_isSilent_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; uint8_t v___y_2559_; lean_object* v___y_2560_; uint8_t v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; uint8_t v___y_2620_; lean_object* v___y_2621_; uint8_t v___y_2622_; uint8_t v___y_2623_; lean_object* v___y_2624_; uint8_t v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; uint8_t v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2656_; uint8_t v___y_2657_; uint8_t v___y_2658_; uint8_t v___x_2673_; uint8_t v___y_2675_; uint8_t v___y_2676_; uint8_t v___y_2677_; uint8_t v___y_2679_; uint8_t v___x_2691_; 
v___x_2673_ = 2;
v___x_2691_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2550_, v___x_2673_);
if (v___x_2691_ == 0)
{
v___y_2679_ = v___x_2691_;
goto v___jp_2678_;
}
else
{
uint8_t v___x_2692_; 
lean_inc_ref(v_msgData_2549_);
v___x_2692_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2549_);
v___y_2679_ = v___x_2692_;
goto v___jp_2678_;
}
v___jp_2555_:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Elab_Command_getScope___redArg(v___y_2563_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref(v___x_2564_);
v___x_2566_ = l_Lean_Elab_Command_getScope___redArg(v___y_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2602_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2602_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2602_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v_currNamespace_2572_; lean_object* v_openDecls_2573_; lean_object* v_env_2574_; lean_object* v_messages_2575_; lean_object* v_scopes_2576_; lean_object* v_usedQuotCtxts_2577_; lean_object* v_nextMacroScope_2578_; lean_object* v_maxRecDepth_2579_; lean_object* v_ngen_2580_; lean_object* v_auxDeclNGen_2581_; lean_object* v_infoState_2582_; lean_object* v_traceState_2583_; lean_object* v_snapshotTasks_2584_; lean_object* v_newDecls_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2601_; 
v___x_2571_ = lean_st_ref_take(v___y_2563_);
v_currNamespace_2572_ = lean_ctor_get(v_a_2565_, 2);
lean_inc(v_currNamespace_2572_);
lean_dec(v_a_2565_);
v_openDecls_2573_ = lean_ctor_get(v_a_2567_, 3);
lean_inc(v_openDecls_2573_);
lean_dec(v_a_2567_);
v_env_2574_ = lean_ctor_get(v___x_2571_, 0);
v_messages_2575_ = lean_ctor_get(v___x_2571_, 1);
v_scopes_2576_ = lean_ctor_get(v___x_2571_, 2);
v_usedQuotCtxts_2577_ = lean_ctor_get(v___x_2571_, 3);
v_nextMacroScope_2578_ = lean_ctor_get(v___x_2571_, 4);
v_maxRecDepth_2579_ = lean_ctor_get(v___x_2571_, 5);
v_ngen_2580_ = lean_ctor_get(v___x_2571_, 6);
v_auxDeclNGen_2581_ = lean_ctor_get(v___x_2571_, 7);
v_infoState_2582_ = lean_ctor_get(v___x_2571_, 8);
v_traceState_2583_ = lean_ctor_get(v___x_2571_, 9);
v_snapshotTasks_2584_ = lean_ctor_get(v___x_2571_, 10);
v_newDecls_2585_ = lean_ctor_get(v___x_2571_, 11);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2587_ = v___x_2571_;
v_isShared_2588_ = v_isSharedCheck_2601_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_newDecls_2585_);
lean_inc(v_snapshotTasks_2584_);
lean_inc(v_traceState_2583_);
lean_inc(v_infoState_2582_);
lean_inc(v_auxDeclNGen_2581_);
lean_inc(v_ngen_2580_);
lean_inc(v_maxRecDepth_2579_);
lean_inc(v_nextMacroScope_2578_);
lean_inc(v_usedQuotCtxts_2577_);
lean_inc(v_scopes_2576_);
lean_inc(v_messages_2575_);
lean_inc(v_env_2574_);
lean_dec(v___x_2571_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2601_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_currNamespace_2572_);
lean_ctor_set(v___x_2589_, 1, v_openDecls_2573_);
v___x_2590_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___y_2556_);
lean_inc_ref(v___y_2558_);
lean_inc_ref(v___y_2562_);
v___x_2591_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2591_, 0, v___y_2562_);
lean_ctor_set(v___x_2591_, 1, v___y_2557_);
lean_ctor_set(v___x_2591_, 2, v___y_2560_);
lean_ctor_set(v___x_2591_, 3, v___y_2558_);
lean_ctor_set(v___x_2591_, 4, v___x_2590_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*5, v___y_2561_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*5 + 1, v___y_2559_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*5 + 2, v_isSilent_2551_);
v___x_2592_ = l_Lean_MessageLog_add(v___x_2591_, v_messages_2575_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v___x_2592_);
v___x_2594_ = v___x_2587_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_env_2574_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2600_, 2, v_scopes_2576_);
lean_ctor_set(v_reuseFailAlloc_2600_, 3, v_usedQuotCtxts_2577_);
lean_ctor_set(v_reuseFailAlloc_2600_, 4, v_nextMacroScope_2578_);
lean_ctor_set(v_reuseFailAlloc_2600_, 5, v_maxRecDepth_2579_);
lean_ctor_set(v_reuseFailAlloc_2600_, 6, v_ngen_2580_);
lean_ctor_set(v_reuseFailAlloc_2600_, 7, v_auxDeclNGen_2581_);
lean_ctor_set(v_reuseFailAlloc_2600_, 8, v_infoState_2582_);
lean_ctor_set(v_reuseFailAlloc_2600_, 9, v_traceState_2583_);
lean_ctor_set(v_reuseFailAlloc_2600_, 10, v_snapshotTasks_2584_);
lean_ctor_set(v_reuseFailAlloc_2600_, 11, v_newDecls_2585_);
v___x_2594_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = lean_st_ref_set(v___y_2563_, v___x_2594_);
v___x_2596_ = lean_box(0);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2596_);
v___x_2598_ = v___x_2569_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v_a_2565_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
v_a_2603_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2566_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2566_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
v_a_2611_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2564_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2564_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
v___jp_2619_:
{
lean_object* v_fileName_2625_; lean_object* v_fileMap_2626_; uint8_t v_suppressElabErrors_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2646_; 
v_fileName_2625_ = lean_ctor_get(v___y_2552_, 0);
v_fileMap_2626_ = lean_ctor_get(v___y_2552_, 1);
v_suppressElabErrors_2627_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*10);
v___x_2628_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2549_);
v___x_2629_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2628_, v___y_2553_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2646_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2646_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_inc_ref_n(v_fileMap_2626_, 2);
v___x_2634_ = l_Lean_FileMap_toPosition(v_fileMap_2626_, v___y_2621_);
lean_dec(v___y_2621_);
v___x_2635_ = l_Lean_FileMap_toPosition(v_fileMap_2626_, v___y_2624_);
lean_dec(v___y_2624_);
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2627_ == 0)
{
lean_del_object(v___x_2632_);
v___y_2556_ = v_a_2630_;
v___y_2557_ = v___x_2634_;
v___y_2558_ = v___x_2637_;
v___y_2559_ = v___y_2622_;
v___y_2560_ = v___x_2636_;
v___y_2561_ = v___y_2623_;
v___y_2562_ = v_fileName_2625_;
v___y_2563_ = v___y_2553_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___f_2640_; uint8_t v___x_2641_; 
v___x_2638_ = lean_box(v___y_2620_);
v___x_2639_ = lean_box(v_suppressElabErrors_2627_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2640_, 0, v___x_2638_);
lean_closure_set(v___f_2640_, 1, v___x_2639_);
lean_inc(v_a_2630_);
v___x_2641_ = l_Lean_MessageData_hasTag(v___f_2640_, v_a_2630_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
lean_dec_ref(v___x_2636_);
lean_dec_ref(v___x_2634_);
lean_dec(v_a_2630_);
v___x_2642_ = lean_box(0);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 0, v___x_2642_);
v___x_2644_ = v___x_2632_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
else
{
lean_del_object(v___x_2632_);
v___y_2556_ = v_a_2630_;
v___y_2557_ = v___x_2634_;
v___y_2558_ = v___x_2637_;
v___y_2559_ = v___y_2622_;
v___y_2560_ = v___x_2636_;
v___y_2561_ = v___y_2623_;
v___y_2562_ = v_fileName_2625_;
v___y_2563_ = v___y_2553_;
goto v___jp_2555_;
}
}
}
}
v___jp_2647_:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Syntax_getTailPos_x3f(v___y_2649_, v___y_2651_);
lean_dec(v___y_2649_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_inc(v___y_2652_);
v___y_2620_ = v___y_2648_;
v___y_2621_ = v___y_2652_;
v___y_2622_ = v___y_2650_;
v___y_2623_ = v___y_2651_;
v___y_2624_ = v___y_2652_;
goto v___jp_2619_;
}
else
{
lean_object* v_val_2654_; 
v_val_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_val_2654_);
lean_dec_ref(v___x_2653_);
v___y_2620_ = v___y_2648_;
v___y_2621_ = v___y_2652_;
v___y_2622_ = v___y_2650_;
v___y_2623_ = v___y_2651_;
v___y_2624_ = v_val_2654_;
goto v___jp_2619_;
}
}
v___jp_2655_:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Elab_Command_getRef___redArg(v___y_2552_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_ref_2661_; lean_object* v___x_2662_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
v_ref_2661_ = l_Lean_replaceRef(v_ref_2548_, v_a_2660_);
lean_dec(v_a_2660_);
v___x_2662_ = l_Lean_Syntax_getPos_x3f(v_ref_2661_, v___y_2657_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_unsigned_to_nat(0u);
v___y_2648_ = v___y_2656_;
v___y_2649_ = v_ref_2661_;
v___y_2650_ = v___y_2658_;
v___y_2651_ = v___y_2657_;
v___y_2652_ = v___x_2663_;
goto v___jp_2647_;
}
else
{
lean_object* v_val_2664_; 
v_val_2664_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_val_2664_);
lean_dec_ref(v___x_2662_);
v___y_2648_ = v___y_2656_;
v___y_2649_ = v_ref_2661_;
v___y_2650_ = v___y_2658_;
v___y_2651_ = v___y_2657_;
v___y_2652_ = v_val_2664_;
goto v___jp_2647_;
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec_ref(v_msgData_2549_);
v_a_2665_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2659_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2659_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
v___jp_2674_:
{
if (v___y_2677_ == 0)
{
v___y_2656_ = v___y_2675_;
v___y_2657_ = v___y_2676_;
v___y_2658_ = v_severity_2550_;
goto v___jp_2655_;
}
else
{
v___y_2656_ = v___y_2675_;
v___y_2657_ = v___y_2676_;
v___y_2658_ = v___x_2673_;
goto v___jp_2655_;
}
}
v___jp_2678_:
{
if (v___y_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v_scopes_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v_opts_2684_; uint8_t v___x_2685_; uint8_t v___x_2686_; 
v___x_2680_ = lean_st_ref_get(v___y_2553_);
v_scopes_2681_ = lean_ctor_get(v___x_2680_, 2);
lean_inc(v_scopes_2681_);
lean_dec(v___x_2680_);
v___x_2682_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2683_ = l_List_head_x21___redArg(v___x_2682_, v_scopes_2681_);
lean_dec(v_scopes_2681_);
v_opts_2684_ = lean_ctor_get(v___x_2683_, 1);
lean_inc_ref(v_opts_2684_);
lean_dec(v___x_2683_);
v___x_2685_ = 1;
v___x_2686_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2550_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_dec_ref(v_opts_2684_);
v___y_2675_ = v___y_2679_;
v___y_2676_ = v___y_2679_;
v___y_2677_ = v___x_2686_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2687_ = l_Lean_warningAsError;
v___x_2688_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2684_, v___x_2687_);
lean_dec_ref(v_opts_2684_);
v___y_2675_ = v___y_2679_;
v___y_2676_ = v___y_2679_;
v___y_2677_ = v___x_2688_;
goto v___jp_2674_;
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec_ref(v_msgData_2549_);
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___boxed(lean_object* v_ref_2693_, lean_object* v_msgData_2694_, lean_object* v_severity_2695_, lean_object* v_isSilent_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
uint8_t v_severity_boxed_2700_; uint8_t v_isSilent_boxed_2701_; lean_object* v_res_2702_; 
v_severity_boxed_2700_ = lean_unbox(v_severity_2695_);
v_isSilent_boxed_2701_ = lean_unbox(v_isSilent_2696_);
v_res_2702_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(v_ref_2693_, v_msgData_2694_, v_severity_boxed_2700_, v_isSilent_boxed_2701_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v_ref_2693_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(lean_object* v_msgData_2703_, uint8_t v_severity_2704_, uint8_t v_isSilent_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Elab_Command_getRef___redArg(v___y_2706_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___x_2711_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(v_a_2710_, v_msgData_2703_, v_severity_2704_, v_isSilent_2705_, v___y_2706_, v___y_2707_);
lean_dec(v_a_2710_);
return v___x_2711_;
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v_msgData_2703_);
v_a_2712_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2709_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2709_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28___boxed(lean_object* v_msgData_2720_, lean_object* v_severity_2721_, lean_object* v_isSilent_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v_severity_boxed_2726_; uint8_t v_isSilent_boxed_2727_; lean_object* v_res_2728_; 
v_severity_boxed_2726_ = lean_unbox(v_severity_2721_);
v_isSilent_boxed_2727_ = lean_unbox(v_isSilent_2722_);
v_res_2728_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(v_msgData_2720_, v_severity_boxed_2726_, v_isSilent_boxed_2727_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
uint8_t v___x_2733_; uint8_t v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = 0;
v___x_2734_ = 0;
v___x_2735_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(v_msgData_2729_, v___x_2733_, v___x_2734_, v___y_2730_, v___y_2731_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(lean_object* v_hi_2741_, lean_object* v_pivot_2742_, lean_object* v_as_2743_, lean_object* v_i_2744_, lean_object* v_k_2745_){
_start:
{
uint8_t v___x_2746_; 
v___x_2746_ = lean_nat_dec_lt(v_k_2745_, v_hi_2741_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v_k_2745_);
lean_dec_ref(v_pivot_2742_);
v___x_2747_ = lean_array_fswap(v_as_2743_, v_i_2744_, v_hi_2741_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v_i_2744_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
return v___x_2748_;
}
else
{
lean_object* v___x_2749_; lean_object* v_fst_2750_; lean_object* v_fst_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2749_ = lean_array_fget_borrowed(v_as_2743_, v_k_2745_);
v_fst_2750_ = lean_ctor_get(v___x_2749_, 0);
v_fst_2751_ = lean_ctor_get(v_pivot_2742_, 0);
lean_inc(v_fst_2750_);
v___x_2752_ = l_Lean_Name_toString(v_fst_2750_, v___x_2746_);
lean_inc(v_fst_2751_);
v___x_2753_ = l_Lean_Name_toString(v_fst_2751_, v___x_2746_);
v___x_2754_ = lean_string_dec_lt(v___x_2752_, v___x_2753_);
lean_dec_ref(v___x_2753_);
lean_dec_ref(v___x_2752_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_unsigned_to_nat(1u);
v___x_2756_ = lean_nat_add(v_k_2745_, v___x_2755_);
lean_dec(v_k_2745_);
v_k_2745_ = v___x_2756_;
goto _start;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = lean_array_fswap(v_as_2743_, v_i_2744_, v_k_2745_);
v___x_2759_ = lean_unsigned_to_nat(1u);
v___x_2760_ = lean_nat_add(v_i_2744_, v___x_2759_);
lean_dec(v_i_2744_);
v___x_2761_ = lean_nat_add(v_k_2745_, v___x_2759_);
lean_dec(v_k_2745_);
v_as_2743_ = v___x_2758_;
v_i_2744_ = v___x_2760_;
v_k_2745_ = v___x_2761_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg___boxed(lean_object* v_hi_2763_, lean_object* v_pivot_2764_, lean_object* v_as_2765_, lean_object* v_i_2766_, lean_object* v_k_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(v_hi_2763_, v_pivot_2764_, v_as_2765_, v_i_2766_, v_k_2767_);
lean_dec(v_hi_2763_);
return v_res_2768_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(uint8_t v___x_2769_, lean_object* v_x1_2770_, lean_object* v_x2_2771_){
_start:
{
lean_object* v_fst_2772_; lean_object* v_fst_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v_fst_2772_ = lean_ctor_get(v_x1_2770_, 0);
lean_inc(v_fst_2772_);
lean_dec_ref(v_x1_2770_);
v_fst_2773_ = lean_ctor_get(v_x2_2771_, 0);
lean_inc(v_fst_2773_);
lean_dec_ref(v_x2_2771_);
v___x_2774_ = l_Lean_Name_toString(v_fst_2772_, v___x_2769_);
v___x_2775_ = l_Lean_Name_toString(v_fst_2773_, v___x_2769_);
v___x_2776_ = lean_string_dec_lt(v___x_2774_, v___x_2775_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v___x_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0___boxed(lean_object* v___x_2777_, lean_object* v_x1_2778_, lean_object* v_x2_2779_){
_start:
{
uint8_t v___x_20283__boxed_2780_; uint8_t v_res_2781_; lean_object* v_r_2782_; 
v___x_20283__boxed_2780_ = lean_unbox(v___x_2777_);
v_res_2781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_20283__boxed_2780_, v_x1_2778_, v_x2_2779_);
v_r_2782_ = lean_box(v_res_2781_);
return v_r_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object* v_n_2783_, lean_object* v_as_2784_, lean_object* v_lo_2785_, lean_object* v_hi_2786_){
_start:
{
lean_object* v___y_2788_; uint8_t v___x_2798_; 
v___x_2798_ = lean_nat_dec_lt(v_lo_2785_, v_hi_2786_);
if (v___x_2798_ == 0)
{
lean_dec(v_lo_2785_);
return v_as_2784_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v_mid_2801_; lean_object* v___y_2803_; lean_object* v___y_2809_; lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2799_ = lean_nat_add(v_lo_2785_, v_hi_2786_);
v___x_2800_ = lean_unsigned_to_nat(1u);
v_mid_2801_ = lean_nat_shiftr(v___x_2799_, v___x_2800_);
lean_dec(v___x_2799_);
v___x_2814_ = lean_array_fget_borrowed(v_as_2784_, v_mid_2801_);
v___x_2815_ = lean_array_fget_borrowed(v_as_2784_, v_lo_2785_);
lean_inc(v___x_2815_);
lean_inc(v___x_2814_);
v___x_2816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_2798_, v___x_2814_, v___x_2815_);
if (v___x_2816_ == 0)
{
v___y_2809_ = v_as_2784_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_2817_; 
v___x_2817_ = lean_array_fswap(v_as_2784_, v_lo_2785_, v_mid_2801_);
v___y_2809_ = v___x_2817_;
goto v___jp_2808_;
}
v___jp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2804_ = lean_array_fget_borrowed(v___y_2803_, v_mid_2801_);
v___x_2805_ = lean_array_fget_borrowed(v___y_2803_, v_hi_2786_);
lean_inc(v___x_2805_);
lean_inc(v___x_2804_);
v___x_2806_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_2798_, v___x_2804_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_dec(v_mid_2801_);
v___y_2788_ = v___y_2803_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_array_fswap(v___y_2803_, v_mid_2801_, v_hi_2786_);
lean_dec(v_mid_2801_);
v___y_2788_ = v___x_2807_;
goto v___jp_2787_;
}
}
v___jp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = lean_array_fget_borrowed(v___y_2809_, v_hi_2786_);
v___x_2811_ = lean_array_fget_borrowed(v___y_2809_, v_lo_2785_);
lean_inc(v___x_2811_);
lean_inc(v___x_2810_);
v___x_2812_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_2798_, v___x_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
v___y_2803_ = v___y_2809_;
goto v___jp_2802_;
}
else
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_array_fswap(v___y_2809_, v_lo_2785_, v_hi_2786_);
v___y_2803_ = v___x_2813_;
goto v___jp_2802_;
}
}
}
v___jp_2787_:
{
lean_object* v_pivot_2789_; lean_object* v___x_2790_; lean_object* v_fst_2791_; lean_object* v_snd_2792_; uint8_t v___x_2793_; 
v_pivot_2789_ = lean_array_fget(v___y_2788_, v_hi_2786_);
lean_inc_n(v_lo_2785_, 2);
v___x_2790_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(v_hi_2786_, v_pivot_2789_, v___y_2788_, v_lo_2785_, v_lo_2785_);
v_fst_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_fst_2791_);
v_snd_2792_ = lean_ctor_get(v___x_2790_, 1);
lean_inc(v_snd_2792_);
lean_dec_ref(v___x_2790_);
v___x_2793_ = lean_nat_dec_le(v_hi_2786_, v_fst_2791_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2794_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_n_2783_, v_snd_2792_, v_lo_2785_, v_fst_2791_);
v___x_2795_ = lean_unsigned_to_nat(1u);
v___x_2796_ = lean_nat_add(v_fst_2791_, v___x_2795_);
lean_dec(v_fst_2791_);
v_as_2784_ = v___x_2794_;
v_lo_2785_ = v___x_2796_;
goto _start;
}
else
{
lean_dec(v_fst_2791_);
lean_dec(v_lo_2785_);
return v_snd_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object* v_n_2818_, lean_object* v_as_2819_, lean_object* v_lo_2820_, lean_object* v_hi_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_n_2818_, v_as_2819_, v_lo_2820_, v_hi_2821_);
lean_dec(v_hi_2821_);
lean_dec(v_n_2818_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(lean_object* v_init_2823_, lean_object* v_x_2824_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_object* v_k_2825_; lean_object* v_v_2826_; lean_object* v_l_2827_; lean_object* v_r_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_k_2825_ = lean_ctor_get(v_x_2824_, 1);
v_v_2826_ = lean_ctor_get(v_x_2824_, 2);
v_l_2827_ = lean_ctor_get(v_x_2824_, 3);
v_r_2828_ = lean_ctor_get(v_x_2824_, 4);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v_init_2823_, v_l_2827_);
lean_inc(v_v_2826_);
lean_inc(v_k_2825_);
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v_k_2825_);
lean_ctor_set(v___x_2830_, 1, v_v_2826_);
v___x_2831_ = lean_array_push(v___x_2829_, v___x_2830_);
v_init_2823_ = v___x_2831_;
v_x_2824_ = v_r_2828_;
goto _start;
}
else
{
return v_init_2823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27___boxed(lean_object* v_init_2833_, lean_object* v_x_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v_init_2833_, v_x_2834_);
lean_dec(v_x_2834_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(lean_object* v_init_2836_, lean_object* v_x_2837_){
_start:
{
if (lean_obj_tag(v_x_2837_) == 0)
{
lean_object* v_k_2839_; lean_object* v_v_2840_; lean_object* v_l_2841_; lean_object* v_r_2842_; lean_object* v___x_2843_; lean_object* v_a_2844_; lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_k_2839_ = lean_ctor_get(v_x_2837_, 1);
lean_inc(v_k_2839_);
v_v_2840_ = lean_ctor_get(v_x_2837_, 2);
lean_inc(v_v_2840_);
v_l_2841_ = lean_ctor_get(v_x_2837_, 3);
lean_inc(v_l_2841_);
v_r_2842_ = lean_ctor_get(v_x_2837_, 4);
lean_inc(v_r_2842_);
lean_dec_ref(v_x_2837_);
v___x_2843_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v_init_2836_, v_l_2841_);
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref(v___x_2843_);
v_a_2845_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_a_2845_);
lean_dec(v_a_2844_);
v___x_2846_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2839_, v_v_2840_, v_a_2845_);
v_init_2836_ = v___x_2846_;
v_x_2837_ = v_r_2842_;
goto _start;
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_init_2836_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg___boxed(lean_object* v_init_2850_, lean_object* v_x_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v_init_2850_, v_x_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(lean_object* v_as_2854_, size_t v_sz_2855_, size_t v_i_2856_, lean_object* v_b_2857_){
_start:
{
uint8_t v___x_2859_; 
v___x_2859_ = lean_usize_dec_lt(v_i_2856_, v_sz_2855_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_b_2857_);
return v___x_2860_;
}
else
{
lean_object* v_a_2861_; lean_object* v_fst_2862_; lean_object* v_snd_2863_; lean_object* v_found_2864_; size_t v___x_2865_; size_t v___x_2866_; 
v_a_2861_ = lean_array_uget_borrowed(v_as_2854_, v_i_2856_);
v_fst_2862_ = lean_ctor_get(v_a_2861_, 0);
v_snd_2863_ = lean_ctor_get(v_a_2861_, 1);
lean_inc(v_snd_2863_);
lean_inc(v_fst_2862_);
v_found_2864_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2862_, v_snd_2863_, v_b_2857_);
v___x_2865_ = ((size_t)1ULL);
v___x_2866_ = lean_usize_add(v_i_2856_, v___x_2865_);
v_i_2856_ = v___x_2866_;
v_b_2857_ = v_found_2864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg___boxed(lean_object* v_as_2868_, lean_object* v_sz_2869_, lean_object* v_i_2870_, lean_object* v_b_2871_, lean_object* v___y_2872_){
_start:
{
size_t v_sz_boxed_2873_; size_t v_i_boxed_2874_; lean_object* v_res_2875_; 
v_sz_boxed_2873_ = lean_unbox_usize(v_sz_2869_);
lean_dec(v_sz_2869_);
v_i_boxed_2874_ = lean_unbox_usize(v_i_2870_);
lean_dec(v_i_2870_);
v_res_2875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(v_as_2868_, v_sz_boxed_2873_, v_i_boxed_2874_, v_b_2871_);
lean_dec_ref(v_as_2868_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_as_2876_, size_t v_sz_2877_, size_t v_i_2878_, lean_object* v_b_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_usize_dec_lt(v_i_2878_, v_sz_2877_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v_b_2879_);
return v___x_2884_;
}
else
{
lean_object* v_a_2885_; size_t v_sz_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
v_a_2885_ = lean_array_uget_borrowed(v_as_2876_, v_i_2878_);
v_sz_2886_ = lean_array_size(v_a_2885_);
v___x_2887_ = ((size_t)0ULL);
v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(v_a_2885_, v_sz_2886_, v___x_2887_, v_b_2879_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; size_t v___x_2890_; size_t v___x_2891_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref(v___x_2888_);
v___x_2890_ = ((size_t)1ULL);
v___x_2891_ = lean_usize_add(v_i_2878_, v___x_2890_);
v_i_2878_ = v___x_2891_;
v_b_2879_ = v_a_2889_;
goto _start;
}
else
{
return v___x_2888_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_as_2893_, lean_object* v_sz_2894_, lean_object* v_i_2895_, lean_object* v_b_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
size_t v_sz_boxed_2900_; size_t v_i_boxed_2901_; lean_object* v_res_2902_; 
v_sz_boxed_2900_ = lean_unbox_usize(v_sz_2894_);
lean_dec(v_sz_2894_);
v_i_boxed_2901_ = lean_unbox_usize(v_i_2895_);
lean_dec(v_i_2895_);
v_res_2902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_as_2893_, v_sz_boxed_2900_, v_i_boxed_2901_, v_b_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_as_2893_);
return v_res_2902_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_box(1);
v___x_2904_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___y_2911_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___x_2926_; lean_object* v_env_2927_; lean_object* v___x_2928_; lean_object* v_toEnvExtension_2929_; lean_object* v_asyncMode_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v_a_2936_; lean_object* v_a_2938_; lean_object* v_a_2961_; 
v___x_2926_ = lean_st_ref_get(v___y_2908_);
v_env_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc_ref_n(v_env_2927_, 2);
lean_dec(v___x_2926_);
v___x_2928_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2929_ = lean_ctor_get(v___x_2928_, 0);
v_asyncMode_2930_ = lean_ctor_get(v_toEnvExtension_2929_, 2);
v___x_2931_ = lean_box(1);
v___x_2932_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2933_ = lean_box(0);
v___x_2934_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2931_, v___x_2928_, v_env_2927_, v_asyncMode_2930_, v___x_2933_);
v___x_2935_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v___x_2931_, v___x_2934_);
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref(v___x_2935_);
v_a_2961_ = lean_ctor_get(v_a_2936_, 0);
lean_inc(v_a_2961_);
lean_dec(v_a_2936_);
v_a_2938_ = v_a_2961_;
goto v___jp_2937_;
v___jp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_array_to_list(v___y_2911_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
v___jp_2914_:
{
lean_object* v___x_2919_; 
v___x_2919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v___y_2917_, v___y_2916_, v___y_2915_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec(v___y_2917_);
v___y_2911_ = v___x_2919_;
goto v___jp_2910_;
}
v___jp_2920_:
{
uint8_t v___x_2925_; 
v___x_2925_ = lean_nat_dec_le(v___y_2924_, v___y_2921_);
if (v___x_2925_ == 0)
{
lean_dec(v___y_2921_);
lean_inc(v___y_2924_);
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2922_;
v___y_2917_ = v___y_2923_;
v___y_2918_ = v___y_2924_;
goto v___jp_2914_;
}
else
{
v___y_2915_ = v___y_2924_;
v___y_2916_ = v___y_2922_;
v___y_2917_ = v___y_2923_;
v___y_2918_ = v___y_2921_;
goto v___jp_2914_;
}
}
v___jp_2937_:
{
lean_object* v___x_2939_; lean_object* v_importedEntries_2940_; size_t v_sz_2941_; size_t v___x_2942_; lean_object* v___x_2943_; 
v___x_2939_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2932_, v_toEnvExtension_2929_, v_env_2927_, v_asyncMode_2930_, v___x_2933_);
v_importedEntries_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_ref(v_importedEntries_2940_);
lean_dec(v___x_2939_);
v_sz_2941_ = lean_array_size(v_importedEntries_2940_);
v___x_2942_ = ((size_t)0ULL);
v___x_2943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_importedEntries_2940_, v_sz_2941_, v___x_2942_, v_a_2938_, v___y_2907_, v___y_2908_);
lean_dec_ref(v_importedEntries_2940_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v_arr_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2947_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v___x_2946_, v_a_2944_);
lean_dec(v_a_2944_);
v___x_2948_ = lean_array_get_size(v_arr_2947_);
v___x_2949_ = lean_nat_dec_eq(v___x_2948_, v___x_2945_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = lean_unsigned_to_nat(1u);
v___x_2951_ = lean_nat_sub(v___x_2948_, v___x_2950_);
v___x_2952_ = lean_nat_dec_le(v___x_2945_, v___x_2951_);
if (v___x_2952_ == 0)
{
lean_inc(v___x_2951_);
v___y_2921_ = v___x_2951_;
v___y_2922_ = v_arr_2947_;
v___y_2923_ = v___x_2948_;
v___y_2924_ = v___x_2951_;
goto v___jp_2920_;
}
else
{
v___y_2921_ = v___x_2951_;
v___y_2922_ = v_arr_2947_;
v___y_2923_ = v___x_2948_;
v___y_2924_ = v___x_2945_;
goto v___jp_2920_;
}
}
else
{
v___y_2911_ = v_arr_2947_;
goto v___jp_2910_;
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
v_a_2953_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2943_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2943_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2966_, lean_object* v_k_2967_, lean_object* v_fallback_2968_){
_start:
{
if (lean_obj_tag(v_t_2966_) == 0)
{
lean_object* v_k_2969_; lean_object* v_v_2970_; lean_object* v_l_2971_; lean_object* v_r_2972_; uint8_t v___x_2973_; 
v_k_2969_ = lean_ctor_get(v_t_2966_, 1);
v_v_2970_ = lean_ctor_get(v_t_2966_, 2);
v_l_2971_ = lean_ctor_get(v_t_2966_, 3);
v_r_2972_ = lean_ctor_get(v_t_2966_, 4);
v___x_2973_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2967_, v_k_2969_);
switch(v___x_2973_)
{
case 0:
{
v_t_2966_ = v_l_2971_;
goto _start;
}
case 1:
{
lean_inc(v_v_2970_);
return v_v_2970_;
}
default: 
{
v_t_2966_ = v_r_2972_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2968_);
return v_fallback_2968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2976_, lean_object* v_k_2977_, lean_object* v_fallback_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2976_, v_k_2977_, v_fallback_2978_);
lean_dec(v_fallback_2978_);
lean_dec(v_k_2977_);
lean_dec(v_t_2976_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2980_, size_t v_sz_2981_, size_t v_i_2982_, lean_object* v_b_2983_){
_start:
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_usize_dec_lt(v_i_2982_, v_sz_2981_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2983_);
return v___x_2986_;
}
else
{
lean_object* v_a_2987_; lean_object* v_fst_2988_; lean_object* v_snd_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; size_t v___x_2994_; size_t v___x_2995_; 
v_a_2987_ = lean_array_uget_borrowed(v_as_2980_, v_i_2982_);
v_fst_2988_ = lean_ctor_get(v_a_2987_, 0);
v_snd_2989_ = lean_ctor_get(v_a_2987_, 1);
v___x_2990_ = l_Lean_NameSet_empty;
v___x_2991_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2983_, v_snd_2989_, v___x_2990_);
lean_inc(v_fst_2988_);
v___x_2992_ = l_Lean_NameSet_insert(v___x_2991_, v_fst_2988_);
lean_inc(v_snd_2989_);
v___x_2993_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2989_, v___x_2992_, v_b_2983_);
v___x_2994_ = ((size_t)1ULL);
v___x_2995_ = lean_usize_add(v_i_2982_, v___x_2994_);
v_i_2982_ = v___x_2995_;
v_b_2983_ = v___x_2993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2997_, lean_object* v_sz_2998_, lean_object* v_i_2999_, lean_object* v_b_3000_, lean_object* v___y_3001_){
_start:
{
size_t v_sz_boxed_3002_; size_t v_i_boxed_3003_; lean_object* v_res_3004_; 
v_sz_boxed_3002_ = lean_unbox_usize(v_sz_2998_);
lean_dec(v_sz_2998_);
v_i_boxed_3003_ = lean_unbox_usize(v_i_2999_);
lean_dec(v_i_2999_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2997_, v_sz_boxed_3002_, v_i_boxed_3003_, v_b_3000_);
lean_dec_ref(v_as_2997_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_3005_, size_t v_sz_3006_, size_t v_i_3007_, lean_object* v_b_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
uint8_t v___x_3012_; 
v___x_3012_ = lean_usize_dec_lt(v_i_3007_, v_sz_3006_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_b_3008_);
return v___x_3013_;
}
else
{
lean_object* v_a_3014_; size_t v_sz_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v_a_3014_ = lean_array_uget_borrowed(v_as_3005_, v_i_3007_);
v_sz_3015_ = lean_array_size(v_a_3014_);
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_3014_, v_sz_3015_, v___x_3016_, v_b_3008_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; size_t v___x_3019_; size_t v___x_3020_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = ((size_t)1ULL);
v___x_3020_ = lean_usize_add(v_i_3007_, v___x_3019_);
v_i_3007_ = v___x_3020_;
v_b_3008_ = v_a_3018_;
goto _start;
}
else
{
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_3022_, lean_object* v_sz_3023_, lean_object* v_i_3024_, lean_object* v_b_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
size_t v_sz_boxed_3029_; size_t v_i_boxed_3030_; lean_object* v_res_3031_; 
v_sz_boxed_3029_ = lean_unbox_usize(v_sz_3023_);
lean_dec(v_sz_3023_);
v_i_boxed_3030_ = lean_unbox_usize(v_i_3024_);
lean_dec(v_i_3024_);
v_res_3031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_3022_, v_sz_boxed_3029_, v_i_boxed_3030_, v_b_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v_as_3022_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_3032_, size_t v_i_3033_, size_t v_stop_3034_, lean_object* v_b_3035_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_eq(v_i_3033_, v_stop_3034_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v_fst_3038_; lean_object* v_snd_3039_; lean_object* v___x_3040_; size_t v___x_3041_; size_t v___x_3042_; 
v___x_3037_ = lean_array_uget_borrowed(v_as_3032_, v_i_3033_);
v_fst_3038_ = lean_ctor_get(v___x_3037_, 0);
v_snd_3039_ = lean_ctor_get(v___x_3037_, 1);
lean_inc(v_snd_3039_);
lean_inc(v_fst_3038_);
v___x_3040_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3038_, v_snd_3039_, v_b_3035_);
v___x_3041_ = ((size_t)1ULL);
v___x_3042_ = lean_usize_add(v_i_3033_, v___x_3041_);
v_i_3033_ = v___x_3042_;
v_b_3035_ = v___x_3040_;
goto _start;
}
else
{
return v_b_3035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_3044_, lean_object* v_i_3045_, lean_object* v_stop_3046_, lean_object* v_b_3047_){
_start:
{
size_t v_i_boxed_3048_; size_t v_stop_boxed_3049_; lean_object* v_res_3050_; 
v_i_boxed_3048_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_stop_boxed_3049_ = lean_unbox_usize(v_stop_3046_);
lean_dec(v_stop_3046_);
v_res_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_3044_, v_i_boxed_3048_, v_stop_boxed_3049_, v_b_3047_);
lean_dec_ref(v_as_3044_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_3051_, size_t v_i_3052_, size_t v_stop_3053_, lean_object* v_b_3054_){
_start:
{
lean_object* v___y_3056_; uint8_t v___x_3060_; 
v___x_3060_ = lean_usize_dec_eq(v_i_3052_, v_stop_3053_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3061_ = lean_array_uget_borrowed(v_as_3051_, v_i_3052_);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = lean_array_get_size(v___x_3061_);
v___x_3064_ = lean_nat_dec_lt(v___x_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
v___y_3056_ = v_b_3054_;
goto v___jp_3055_;
}
else
{
uint8_t v___x_3065_; 
v___x_3065_ = lean_nat_dec_le(v___x_3063_, v___x_3063_);
if (v___x_3065_ == 0)
{
if (v___x_3064_ == 0)
{
v___y_3056_ = v_b_3054_;
goto v___jp_3055_;
}
else
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((size_t)0ULL);
v___x_3067_ = lean_usize_of_nat(v___x_3063_);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_3061_, v___x_3066_, v___x_3067_, v_b_3054_);
v___y_3056_ = v___x_3068_;
goto v___jp_3055_;
}
}
else
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = lean_usize_of_nat(v___x_3063_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_3061_, v___x_3069_, v___x_3070_, v_b_3054_);
v___y_3056_ = v___x_3071_;
goto v___jp_3055_;
}
}
}
else
{
return v_b_3054_;
}
v___jp_3055_:
{
size_t v___x_3057_; size_t v___x_3058_; 
v___x_3057_ = ((size_t)1ULL);
v___x_3058_ = lean_usize_add(v_i_3052_, v___x_3057_);
v_i_3052_ = v___x_3058_;
v_b_3054_ = v___y_3056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_3072_, lean_object* v_i_3073_, lean_object* v_stop_3074_, lean_object* v_b_3075_){
_start:
{
size_t v_i_boxed_3076_; size_t v_stop_boxed_3077_; lean_object* v_res_3078_; 
v_i_boxed_3076_ = lean_unbox_usize(v_i_3073_);
lean_dec(v_i_3073_);
v_stop_boxed_3077_ = lean_unbox_usize(v_stop_3074_);
lean_dec(v_stop_3074_);
v_res_3078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_3072_, v_i_boxed_3076_, v_stop_boxed_3077_, v_b_3075_);
lean_dec_ref(v_as_3072_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; lean_object* v_env_3082_; lean_object* v___x_3083_; lean_object* v_ext_3084_; lean_object* v_toEnvExtension_3085_; lean_object* v_asyncMode_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_categories_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3081_ = lean_st_ref_get(v___y_3079_);
v_env_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc_ref_n(v_env_3082_, 2);
lean_dec(v___x_3081_);
v___x_3083_ = l_Lean_Parser_parserExtension;
v_ext_3084_ = lean_ctor_get(v___x_3083_, 1);
v_toEnvExtension_3085_ = lean_ctor_get(v_ext_3084_, 0);
v_asyncMode_3086_ = lean_ctor_get(v_toEnvExtension_3085_, 2);
v___x_3087_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3088_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3087_, v___x_3083_, v_env_3082_, v_asyncMode_3086_);
v_categories_3089_ = lean_ctor_get(v___x_3088_, 2);
lean_inc_ref(v_categories_3089_);
lean_dec(v___x_3088_);
v___x_3090_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3091_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3089_, v___x_3090_);
lean_dec_ref(v_categories_3089_);
if (lean_obj_tag(v___x_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3129_; 
v_val_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3129_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_val_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3129_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___y_3097_; lean_object* v___x_3106_; lean_object* v_toEnvExtension_3107_; lean_object* v_exportEntriesFn_3108_; lean_object* v_asyncMode_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v_importedEntries_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v_exported_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3106_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3107_ = lean_ctor_get(v___x_3106_, 0);
v_exportEntriesFn_3108_ = lean_ctor_get(v___x_3106_, 4);
v_asyncMode_3109_ = lean_ctor_get(v_toEnvExtension_3107_, 2);
v___x_3110_ = lean_box(1);
v___x_3111_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3112_ = lean_box(0);
lean_inc_ref_n(v_env_3082_, 2);
v___x_3113_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3111_, v_toEnvExtension_3107_, v_env_3082_, v_asyncMode_3109_, v___x_3112_);
v_importedEntries_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc_ref(v_importedEntries_3114_);
lean_dec(v___x_3113_);
v___x_3115_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3110_, v___x_3106_, v_env_3082_, v_asyncMode_3109_, v___x_3112_);
lean_inc_ref(v_exportEntriesFn_3108_);
v___x_3116_ = lean_apply_2(v_exportEntriesFn_3108_, v_env_3082_, v___x_3115_);
v_exported_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_exported_3117_);
lean_dec_ref(v___x_3116_);
v___x_3118_ = lean_array_push(v_importedEntries_3114_, v_exported_3117_);
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = lean_array_get_size(v___x_3118_);
v___x_3121_ = lean_nat_dec_lt(v___x_3119_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_dec_ref(v___x_3118_);
v___y_3097_ = v___x_3110_;
goto v___jp_3096_;
}
else
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_le(v___x_3120_, v___x_3120_);
if (v___x_3122_ == 0)
{
if (v___x_3121_ == 0)
{
lean_dec_ref(v___x_3118_);
v___y_3097_ = v___x_3110_;
goto v___jp_3096_;
}
else
{
size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((size_t)0ULL);
v___x_3124_ = lean_usize_of_nat(v___x_3120_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3118_, v___x_3123_, v___x_3124_, v___x_3110_);
lean_dec_ref(v___x_3118_);
v___y_3097_ = v___x_3125_;
goto v___jp_3096_;
}
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = ((size_t)0ULL);
v___x_3127_ = lean_usize_of_nat(v___x_3120_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3118_, v___x_3126_, v___x_3127_, v___x_3110_);
lean_dec_ref(v___x_3118_);
v___y_3097_ = v___x_3128_;
goto v___jp_3096_;
}
}
v___jp_3096_:
{
lean_object* v_tables_3098_; lean_object* v_leadingTable_3099_; lean_object* v_trailingTable_3100_; lean_object* v_firstTokens_3101_; lean_object* v_firstTokens_3102_; lean_object* v___x_3104_; 
v_tables_3098_ = lean_ctor_get(v_val_3092_, 2);
v_leadingTable_3099_ = lean_ctor_get(v_tables_3098_, 0);
v_trailingTable_3100_ = lean_ctor_get(v_tables_3098_, 2);
lean_inc(v_trailingTable_3100_);
lean_inc(v_leadingTable_3099_);
lean_inc(v_val_3092_);
v_firstTokens_3101_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3092_, v_leadingTable_3099_, v___y_3097_);
v_firstTokens_3102_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3092_, v_trailingTable_3100_, v_firstTokens_3101_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 0);
lean_ctor_set(v___x_3094_, 0, v_firstTokens_3102_);
v___x_3104_ = v___x_3094_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_firstTokens_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v___x_3091_);
lean_dec_ref(v_env_3082_);
v___x_3130_ = lean_box(1);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3132_);
lean_dec(v___y_3132_);
return v_res_3134_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = lean_box(1);
v___x_3136_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3135_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_3139_ = l_Lean_stringToMessageData(v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_env_3146_; lean_object* v_env_3147_; lean_object* v_env_3148_; lean_object* v___x_3149_; lean_object* v_toEnvExtension_3150_; lean_object* v_exportEntriesFn_3151_; lean_object* v_asyncMode_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v_importedEntries_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3209_; 
v___x_3143_ = lean_st_ref_get(v_a_3141_);
v___x_3144_ = lean_st_ref_get(v_a_3141_);
v___x_3145_ = lean_st_ref_get(v_a_3141_);
v_env_3146_ = lean_ctor_get(v___x_3143_, 0);
lean_inc_ref(v_env_3146_);
lean_dec(v___x_3143_);
v_env_3147_ = lean_ctor_get(v___x_3144_, 0);
lean_inc_ref(v_env_3147_);
lean_dec(v___x_3144_);
v_env_3148_ = lean_ctor_get(v___x_3145_, 0);
lean_inc_ref(v_env_3148_);
lean_dec(v___x_3145_);
v___x_3149_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3150_ = lean_ctor_get(v___x_3149_, 0);
v_exportEntriesFn_3151_ = lean_ctor_get(v___x_3149_, 4);
v_asyncMode_3152_ = lean_ctor_get(v_toEnvExtension_3150_, 2);
v___x_3153_ = lean_box(1);
v___x_3154_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3155_ = lean_box(0);
v___x_3156_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3154_, v_toEnvExtension_3150_, v_env_3146_, v_asyncMode_3152_, v___x_3155_);
v_importedEntries_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_3156_, 1);
lean_dec(v_unused_3210_);
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3209_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_importedEntries_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3209_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_exported_3163_; lean_object* v___x_3164_; size_t v_sz_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3161_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3153_, v___x_3149_, v_env_3148_, v_asyncMode_3152_, v___x_3155_);
lean_inc_ref(v_exportEntriesFn_3151_);
v___x_3162_ = lean_apply_2(v_exportEntriesFn_3151_, v_env_3147_, v___x_3161_);
v_exported_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_exported_3163_);
lean_dec_ref(v___x_3162_);
v___x_3164_ = lean_array_push(v_importedEntries_3157_, v_exported_3163_);
v_sz_3165_ = lean_array_size(v___x_3164_);
v___x_3166_ = ((size_t)0ULL);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_3164_, v_sz_3165_, v___x_3166_, v___x_3153_, v_a_3140_, v_a_3141_);
lean_dec_ref(v___x_3164_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; lean_object* v_a_3170_; lean_object* v___x_3171_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref(v___x_3167_);
v___x_3169_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_3141_);
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v___x_3169_);
v___x_3171_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_3140_, v_a_3141_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = lean_box(0);
v___x_3174_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3170_, v_a_3168_, v_a_3172_, v___x_3173_, v_a_3140_, v_a_3141_);
lean_dec(v_a_3168_);
lean_dec(v_a_3170_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3174_);
v___x_3176_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_3177_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_3178_ = l_Lean_MessageData_joinSep(v_a_3175_, v___x_3177_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set_tag(v___x_3159_, 7);
lean_ctor_set(v___x_3159_, 1, v___x_3178_);
lean_ctor_set(v___x_3159_, 0, v___x_3177_);
v___x_3180_ = v___x_3159_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = l_Lean_MessageData_nestD(v___x_3180_);
v___x_3182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3176_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_3182_, v_a_3140_, v_a_3141_);
return v___x_3183_;
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_del_object(v___x_3159_);
v_a_3185_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3174_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3174_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3170_);
lean_dec(v_a_3168_);
lean_del_object(v___x_3159_);
v_a_3193_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3171_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3171_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3159_);
v_a_3201_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3167_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3167_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3211_, v_a_3212_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3216_, v_a_3217_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_3220_, v_a_3221_, v_a_3222_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v___stx_3220_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_3225_, lean_object* v_t_3226_, lean_object* v_k_3227_, lean_object* v_fallback_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3226_, v_k_3227_, v_fallback_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_3230_, lean_object* v_t_3231_, lean_object* v_k_3232_, lean_object* v_fallback_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_3230_, v_t_3231_, v_k_3232_, v_fallback_3233_);
lean_dec(v_fallback_3233_);
lean_dec(v_k_3232_);
lean_dec(v_t_3231_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_3235_, size_t v_sz_3236_, size_t v_i_3237_, lean_object* v_b_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3235_, v_sz_3236_, v_i_3237_, v_b_3238_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_3243_, lean_object* v_sz_3244_, lean_object* v_i_3245_, lean_object* v_b_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
size_t v_sz_boxed_3250_; size_t v_i_boxed_3251_; lean_object* v_res_3252_; 
v_sz_boxed_3250_ = lean_unbox_usize(v_sz_3244_);
lean_dec(v_sz_3244_);
v_i_boxed_3251_ = lean_unbox_usize(v_i_3245_);
lean_dec(v_i_3245_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_3243_, v_sz_boxed_3250_, v_i_boxed_3251_, v_b_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v_as_3243_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3254_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_3261_, lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v_inst_3264_, lean_object* v_R_3265_, lean_object* v_a_3266_, lean_object* v_b_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3261_, v___x_3262_, v___x_3263_, v_a_3266_, v_b_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_3269_, lean_object* v___x_3270_, lean_object* v___x_3271_, lean_object* v_inst_3272_, lean_object* v_R_3273_, lean_object* v_a_3274_, lean_object* v_b_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_3269_, v___x_3270_, v___x_3271_, v_inst_3272_, v_R_3273_, v_a_3274_, v_b_3275_);
lean_dec_ref(v___x_3270_);
lean_dec_ref(v_val_3269_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_3277_, lean_object* v_t_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_3277_, v_t_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_3280_, lean_object* v_as_3281_, lean_object* v_lo_3282_, lean_object* v_hi_3283_, lean_object* v_w_3284_, lean_object* v_hlo_3285_, lean_object* v_hhi_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3280_, v_as_3281_, v_lo_3282_, v_hi_3283_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_3288_, lean_object* v_as_3289_, lean_object* v_lo_3290_, lean_object* v_hi_3291_, lean_object* v_w_3292_, lean_object* v_hlo_3293_, lean_object* v_hhi_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_3288_, v_as_3289_, v_lo_3290_, v_hi_3291_, v_w_3292_, v_hlo_3293_, v_hhi_3294_);
lean_dec(v_hi_3291_);
lean_dec(v_n_3288_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3297_, v_x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3300_, lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_3300_, v_x_3301_, v_x_3302_);
lean_dec(v_x_3302_);
lean_dec_ref(v_x_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3304_, v___y_3306_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b2_3314_, lean_object* v_k_3315_, lean_object* v_v_3316_, lean_object* v_t_3317_, lean_object* v_hl_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_3315_, v_v_3316_, v_t_3317_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_as_3320_, lean_object* v_as_x27_3321_, lean_object* v_b_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_as_x27_3321_, v_b_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_as_3325_, lean_object* v_as_x27_3326_, lean_object* v_b_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_as_3325_, v_as_x27_3326_, v_b_3327_, v_a_3328_);
lean_dec(v_as_x27_3326_);
lean_dec(v_as_3325_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_00_u03b4_3330_, lean_object* v_t_3331_, lean_object* v_k_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_3331_, v_k_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___boxed(lean_object* v_00_u03b4_3334_, lean_object* v_t_3335_, lean_object* v_k_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v_00_u03b4_3334_, v_t_3335_, v_k_3336_);
lean_dec(v_k_3336_);
lean_dec(v_t_3335_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(lean_object* v_00_u03b2_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_3339_, v_x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___boxed(lean_object* v_00_u03b2_3342_, lean_object* v_x_3343_, lean_object* v_x_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(v_00_u03b2_3342_, v_x_3343_, v_x_3344_);
lean_dec(v_x_3344_);
lean_dec_ref(v_x_3343_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19(lean_object* v_n_3346_, lean_object* v_lo_3347_, lean_object* v_hi_3348_, lean_object* v_hhi_3349_, lean_object* v_pivot_3350_, lean_object* v_as_3351_, lean_object* v_i_3352_, lean_object* v_k_3353_, lean_object* v_ilo_3354_, lean_object* v_ik_3355_, lean_object* v_w_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(v_hi_3348_, v_pivot_3350_, v_as_3351_, v_i_3352_, v_k_3353_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___boxed(lean_object* v_n_3358_, lean_object* v_lo_3359_, lean_object* v_hi_3360_, lean_object* v_hhi_3361_, lean_object* v_pivot_3362_, lean_object* v_as_3363_, lean_object* v_i_3364_, lean_object* v_k_3365_, lean_object* v_ilo_3366_, lean_object* v_ik_3367_, lean_object* v_w_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19(v_n_3358_, v_lo_3359_, v_hi_3360_, v_hhi_3361_, v_pivot_3362_, v_as_3363_, v_i_3364_, v_k_3365_, v_ilo_3366_, v_ik_3367_, v_w_3368_);
lean_dec(v_hi_3360_);
lean_dec(v_lo_3359_);
lean_dec(v_n_3358_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_as_3370_, size_t v_sz_3371_, size_t v_i_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(v_as_3370_, v_sz_3371_, v_i_3372_, v_b_3373_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_as_3378_, lean_object* v_sz_3379_, lean_object* v_i_3380_, lean_object* v_b_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
size_t v_sz_boxed_3385_; size_t v_i_boxed_3386_; lean_object* v_res_3387_; 
v_sz_boxed_3385_ = lean_unbox_usize(v_sz_3379_);
lean_dec(v_sz_3379_);
v_i_boxed_3386_ = lean_unbox_usize(v_i_3380_);
lean_dec(v_i_3380_);
v_res_3387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_as_3378_, v_sz_boxed_3385_, v_i_boxed_3386_, v_b_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec_ref(v_as_3378_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3388_, lean_object* v_t_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v_init_3388_, v_t_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3391_, lean_object* v_t_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3391_, v_t_3392_);
lean_dec(v_t_3392_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object* v_n_3394_, lean_object* v_as_3395_, lean_object* v_lo_3396_, lean_object* v_hi_3397_, lean_object* v_w_3398_, lean_object* v_hlo_3399_, lean_object* v_hhi_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_n_3394_, v_as_3395_, v_lo_3396_, v_hi_3397_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object* v_n_3402_, lean_object* v_as_3403_, lean_object* v_lo_3404_, lean_object* v_hi_3405_, lean_object* v_w_3406_, lean_object* v_hlo_3407_, lean_object* v_hhi_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(v_n_3402_, v_as_3403_, v_lo_3404_, v_hi_3405_, v_w_3406_, v_hlo_3407_, v_hhi_3408_);
lean_dec(v_hi_3405_);
lean_dec(v_n_3402_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25(lean_object* v_init_3410_, lean_object* v_x_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v_init_3410_, v_x_3411_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___boxed(lean_object* v_init_3416_, lean_object* v_x_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25(v_init_3416_, v_x_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3422_, lean_object* v_x_3423_, size_t v_x_3424_, lean_object* v_x_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3423_, v_x_3424_, v_x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3427_, lean_object* v_x_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_){
_start:
{
size_t v_x_21019__boxed_3431_; lean_object* v_res_3432_; 
v_x_21019__boxed_3431_ = lean_unbox_usize(v_x_3429_);
lean_dec(v_x_3429_);
v_res_3432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3427_, v_x_3428_, v_x_21019__boxed_3431_, v_x_3430_);
lean_dec(v_x_3430_);
lean_dec_ref(v_x_3428_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3433_, lean_object* v_k_3434_, lean_object* v_x_3435_, lean_object* v_x_3436_, lean_object* v_x_3437_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3433_, v_k_3434_, v_x_3435_, v_x_3436_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3439_, lean_object* v_k_3440_, lean_object* v_x_3441_, lean_object* v_x_3442_, lean_object* v_x_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3439_, v_k_3440_, v_x_3441_, v_x_3442_, v_x_3443_);
lean_dec_ref(v_k_3440_);
lean_dec_ref(v_as_3439_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object* v_00_u03b2_3445_, lean_object* v_m_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_3446_, v_a_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object* v_00_u03b2_3449_, lean_object* v_m_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(v_00_u03b2_3449_, v_m_3450_, v_a_3451_);
lean_dec(v_a_3451_);
lean_dec_ref(v_m_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29(lean_object* v_n_3453_, lean_object* v_lo_3454_, lean_object* v_hi_3455_, lean_object* v_hhi_3456_, lean_object* v_pivot_3457_, lean_object* v_as_3458_, lean_object* v_i_3459_, lean_object* v_k_3460_, lean_object* v_ilo_3461_, lean_object* v_ik_3462_, lean_object* v_w_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(v_hi_3455_, v_pivot_3457_, v_as_3458_, v_i_3459_, v_k_3460_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___boxed(lean_object* v_n_3465_, lean_object* v_lo_3466_, lean_object* v_hi_3467_, lean_object* v_hhi_3468_, lean_object* v_pivot_3469_, lean_object* v_as_3470_, lean_object* v_i_3471_, lean_object* v_k_3472_, lean_object* v_ilo_3473_, lean_object* v_ik_3474_, lean_object* v_w_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29(v_n_3465_, v_lo_3466_, v_hi_3467_, v_hhi_3468_, v_pivot_3469_, v_as_3470_, v_i_3471_, v_k_3472_, v_ilo_3473_, v_ik_3474_, v_w_3475_);
lean_dec(v_hi_3467_);
lean_dec(v_lo_3466_);
lean_dec(v_n_3465_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3477_, lean_object* v_keys_3478_, lean_object* v_vals_3479_, lean_object* v_heq_3480_, lean_object* v_i_3481_, lean_object* v_k_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3478_, v_vals_3479_, v_i_3481_, v_k_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3484_, lean_object* v_keys_3485_, lean_object* v_vals_3486_, lean_object* v_heq_3487_, lean_object* v_i_3488_, lean_object* v_k_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3484_, v_keys_3485_, v_vals_3486_, v_heq_3487_, v_i_3488_, v_k_3489_);
lean_dec(v_k_3489_);
lean_dec_ref(v_vals_3486_);
lean_dec_ref(v_keys_3485_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object* v_00_u03b2_3491_, lean_object* v_a_3492_, lean_object* v_x_3493_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_3492_, v_x_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object* v_00_u03b2_3495_, lean_object* v_a_3496_, lean_object* v_x_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(v_00_u03b2_3495_, v_a_3496_, v_x_3497_);
lean_dec(v_x_3497_);
lean_dec(v_a_3496_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3513_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3516_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3517_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3513_, v___x_3514_, v___x_3515_, v___x_3516_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3524_ = l_Lean_addBuiltinDocString(v___x_3522_, v___x_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3555_ = l_Lean_addBuiltinDeclarationRanges(v___x_3553_, v___x_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, uint8_t v_includeUnnamed_3561_, lean_object* v_x_3562_, lean_object* v_____s_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v_fst_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3622_; 
v_fst_3569_ = lean_ctor_get(v_x_3562_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_x_3562_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v_x_3562_, 1);
lean_dec(v_unused_3623_);
v___x_3571_ = v_x_3562_;
v_isShared_3572_ = v_isSharedCheck_3622_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_fst_3569_);
lean_dec(v_x_3562_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3622_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v_userName_3574_; lean_object* v___y_3575_; lean_object* v___x_3607_; 
lean_inc(v_fst_3569_);
lean_inc_ref(v_env_3558_);
v___x_3607_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3558_, v_fst_3569_);
if (lean_obj_tag(v___x_3607_) == 1)
{
lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3615_; 
lean_del_object(v___x_3571_);
lean_dec(v_fst_3569_);
lean_dec_ref(v_env_3558_);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v___x_3607_, 0);
lean_dec(v_unused_3616_);
v___x_3609_ = v___x_3607_;
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
else
{
lean_dec(v___x_3607_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3615_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v_____s_3563_);
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_____s_3563_);
v___x_3612_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; 
v___x_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
return v___x_3613_;
}
}
}
else
{
lean_object* v___x_3617_; 
lean_dec(v___x_3607_);
v___x_3617_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_a_3560_, v_fst_3569_);
if (lean_obj_tag(v___x_3617_) == 1)
{
lean_object* v_val_3618_; 
v_val_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_val_3618_);
lean_dec_ref(v___x_3617_);
v_userName_3574_ = v_val_3618_;
v___y_3575_ = v___y_3566_;
goto v___jp_3573_;
}
else
{
lean_dec(v___x_3617_);
if (v_includeUnnamed_3561_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
lean_del_object(v___x_3571_);
lean_dec(v_fst_3569_);
lean_dec_ref(v_env_3558_);
v___x_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_____s_3563_);
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
else
{
lean_object* v___x_3621_; 
lean_inc(v_fst_3569_);
v___x_3621_ = l_Lean_Name_toString(v_fst_3569_, v_includeUnnamed_3561_);
v_userName_3574_ = v___x_3621_;
v___y_3575_ = v___y_3566_;
goto v___jp_3573_;
}
}
}
v___jp_3573_:
{
uint8_t v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = 1;
lean_inc(v_fst_3569_);
lean_inc_ref(v_env_3558_);
v___x_3577_ = l_Lean_findDocString_x3f(v_env_3558_, v_fst_3569_, v___x_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3571_);
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3580_ = v___x_3577_;
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3577_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3582_ = l_Lean_NameSet_empty;
v___x_3583_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3559_, v_fst_3569_, v___x_3582_);
lean_inc(v_fst_3569_);
v___x_3584_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3558_, v_fst_3569_);
v___x_3585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3585_, 0, v_fst_3569_);
lean_ctor_set(v___x_3585_, 1, v_userName_3574_);
lean_ctor_set(v___x_3585_, 2, v___x_3583_);
lean_ctor_set(v___x_3585_, 3, v_a_3578_);
lean_ctor_set(v___x_3585_, 4, v___x_3584_);
v___x_3586_ = lean_array_push(v_____s_3563_, v___x_3585_);
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3587_);
v___x_3589_ = v___x_3580_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v_userName_3574_);
lean_dec(v_fst_3569_);
lean_dec_ref(v_____s_3563_);
lean_dec_ref(v_env_3558_);
v_a_3592_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3594_ = v___x_3577_;
v_isShared_3595_ = v_isSharedCheck_3606_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3577_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3606_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v_ref_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
v_ref_3596_ = lean_ctor_get(v___y_3575_, 5);
v___x_3597_ = lean_io_error_to_string(v_a_3592_);
v___x_3598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
v___x_3599_ = l_Lean_MessageData_ofFormat(v___x_3598_);
lean_inc(v_ref_3596_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v___x_3599_);
lean_ctor_set(v___x_3571_, 0, v_ref_3596_);
v___x_3601_ = v___x_3571_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_ref_3596_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3603_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v___x_3601_);
v___x_3603_ = v___x_3594_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_includeUnnamed_3627_, lean_object* v_x_3628_, lean_object* v_____s_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
uint8_t v_includeUnnamed_boxed_3635_; lean_object* v_res_3636_; 
v_includeUnnamed_boxed_3635_ = lean_unbox(v_includeUnnamed_3627_);
v_res_3636_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3624_, v_a_3625_, v_a_3626_, v_includeUnnamed_boxed_3635_, v_x_3628_, v_____s_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v_a_3626_);
lean_dec(v_a_3625_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3637_, size_t v_sz_3638_, size_t v_i_3639_, lean_object* v_b_3640_){
_start:
{
uint8_t v___x_3642_; 
v___x_3642_ = lean_usize_dec_lt(v_i_3639_, v_sz_3638_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; 
v___x_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3643_, 0, v_b_3640_);
return v___x_3643_;
}
else
{
lean_object* v_a_3644_; lean_object* v_fst_3645_; lean_object* v_snd_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; size_t v___x_3651_; size_t v___x_3652_; 
v_a_3644_ = lean_array_uget_borrowed(v_as_3637_, v_i_3639_);
v_fst_3645_ = lean_ctor_get(v_a_3644_, 0);
v_snd_3646_ = lean_ctor_get(v_a_3644_, 1);
v___x_3647_ = l_Lean_NameSet_empty;
v___x_3648_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3640_, v_fst_3645_, v___x_3647_);
lean_inc(v_snd_3646_);
v___x_3649_ = l_Lean_NameSet_insert(v___x_3648_, v_snd_3646_);
lean_inc(v_fst_3645_);
v___x_3650_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3645_, v___x_3649_, v_b_3640_);
v___x_3651_ = ((size_t)1ULL);
v___x_3652_ = lean_usize_add(v_i_3639_, v___x_3651_);
v_i_3639_ = v___x_3652_;
v_b_3640_ = v___x_3650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3654_, lean_object* v_sz_3655_, lean_object* v_i_3656_, lean_object* v_b_3657_, lean_object* v___y_3658_){
_start:
{
size_t v_sz_boxed_3659_; size_t v_i_boxed_3660_; lean_object* v_res_3661_; 
v_sz_boxed_3659_ = lean_unbox_usize(v_sz_3655_);
lean_dec(v_sz_3655_);
v_i_boxed_3660_ = lean_unbox_usize(v_i_3656_);
lean_dec(v_i_3656_);
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3654_, v_sz_boxed_3659_, v_i_boxed_3660_, v_b_3657_);
lean_dec_ref(v_as_3654_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3662_, size_t v_sz_3663_, size_t v_i_3664_, lean_object* v_b_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v___x_3671_; 
v___x_3671_ = lean_usize_dec_lt(v_i_3664_, v_sz_3663_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v_b_3665_);
return v___x_3672_;
}
else
{
lean_object* v_a_3673_; size_t v_sz_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v_a_3673_ = lean_array_uget_borrowed(v_as_3662_, v_i_3664_);
v_sz_3674_ = lean_array_size(v_a_3673_);
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3673_, v_sz_3674_, v___x_3675_, v_b_3665_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; size_t v___x_3678_; size_t v___x_3679_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___x_3676_);
v___x_3678_ = ((size_t)1ULL);
v___x_3679_ = lean_usize_add(v_i_3664_, v___x_3678_);
v_i_3664_ = v___x_3679_;
v_b_3665_ = v_a_3677_;
goto _start;
}
else
{
return v___x_3676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3681_, lean_object* v_sz_3682_, lean_object* v_i_3683_, lean_object* v_b_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
size_t v_sz_boxed_3690_; size_t v_i_boxed_3691_; lean_object* v_res_3692_; 
v_sz_boxed_3690_ = lean_unbox_usize(v_sz_3682_);
lean_dec(v_sz_3682_);
v_i_boxed_3691_ = lean_unbox_usize(v_i_3683_);
lean_dec(v_i_3683_);
v_res_3692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3681_, v_sz_boxed_3690_, v_i_boxed_3691_, v_b_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_as_3681_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3693_, lean_object* v_keys_3694_, lean_object* v_vals_3695_, lean_object* v_i_3696_, lean_object* v_acc_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = lean_array_get_size(v_keys_3694_);
v___x_3704_ = lean_nat_dec_lt(v_i_3696_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_dec(v_i_3696_);
lean_dec_ref(v_f_3693_);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_acc_3697_);
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
return v___x_3706_;
}
else
{
lean_object* v_k_3707_; lean_object* v_v_3708_; lean_object* v___x_3709_; 
v_k_3707_ = lean_array_fget_borrowed(v_keys_3694_, v_i_3696_);
v_v_3708_ = lean_array_fget_borrowed(v_vals_3695_, v_i_3696_);
lean_inc_ref(v_f_3693_);
lean_inc(v___y_3701_);
lean_inc_ref(v___y_3700_);
lean_inc(v___y_3699_);
lean_inc_ref(v___y_3698_);
lean_inc(v_v_3708_);
lean_inc(v_k_3707_);
v___x_3709_ = lean_apply_8(v_f_3693_, v_acc_3697_, v_k_3707_, v_v_3708_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, lean_box(0));
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
if (lean_obj_tag(v_a_3710_) == 0)
{
lean_dec_ref(v_a_3710_);
lean_dec(v_i_3696_);
lean_dec_ref(v_f_3693_);
return v___x_3709_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec_ref(v___x_3709_);
v_a_3711_ = lean_ctor_get(v_a_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref(v_a_3710_);
v___x_3712_ = lean_unsigned_to_nat(1u);
v___x_3713_ = lean_nat_add(v_i_3696_, v___x_3712_);
lean_dec(v_i_3696_);
v_i_3696_ = v___x_3713_;
v_acc_3697_ = v_a_3711_;
goto _start;
}
}
else
{
lean_dec(v_i_3696_);
lean_dec_ref(v_f_3693_);
return v___x_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3715_, lean_object* v_keys_3716_, lean_object* v_vals_3717_, lean_object* v_i_3718_, lean_object* v_acc_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3715_, v_keys_3716_, v_vals_3717_, v_i_3718_, v_acc_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v_vals_3717_);
lean_dec_ref(v_keys_3716_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3726_, lean_object* v_x_3727_, lean_object* v_x_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
if (lean_obj_tag(v_x_3727_) == 0)
{
lean_object* v_es_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3756_; 
v_es_3734_ = lean_ctor_get(v_x_3727_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_x_3727_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3736_ = v_x_3727_;
v_isShared_3737_ = v_isSharedCheck_3756_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_es_3734_);
lean_dec(v_x_3727_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3756_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3738_ = lean_unsigned_to_nat(0u);
v___x_3739_ = lean_array_get_size(v_es_3734_);
v___x_3740_ = lean_nat_dec_lt(v___x_3738_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v_es_3734_);
lean_dec_ref(v_f_3726_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 1);
lean_ctor_set(v___x_3736_, 0, v_x_3728_);
v___x_3742_ = v___x_3736_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_x_3728_);
v___x_3742_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
return v___x_3743_;
}
}
else
{
uint8_t v___x_3745_; 
v___x_3745_ = lean_nat_dec_le(v___x_3739_, v___x_3739_);
if (v___x_3745_ == 0)
{
if (v___x_3740_ == 0)
{
lean_object* v___x_3747_; 
lean_dec_ref(v_es_3734_);
lean_dec_ref(v_f_3726_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set_tag(v___x_3736_, 1);
lean_ctor_set(v___x_3736_, 0, v_x_3728_);
v___x_3747_ = v___x_3736_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_x_3728_);
v___x_3747_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3748_; 
v___x_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
return v___x_3748_;
}
}
else
{
size_t v___x_3750_; size_t v___x_3751_; lean_object* v___x_3752_; 
lean_del_object(v___x_3736_);
v___x_3750_ = ((size_t)0ULL);
v___x_3751_ = lean_usize_of_nat(v___x_3739_);
v___x_3752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3726_, v_es_3734_, v___x_3750_, v___x_3751_, v_x_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec_ref(v_es_3734_);
return v___x_3752_;
}
}
else
{
size_t v___x_3753_; size_t v___x_3754_; lean_object* v___x_3755_; 
lean_del_object(v___x_3736_);
v___x_3753_ = ((size_t)0ULL);
v___x_3754_ = lean_usize_of_nat(v___x_3739_);
v___x_3755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3726_, v_es_3734_, v___x_3753_, v___x_3754_, v_x_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec_ref(v_es_3734_);
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_ks_3757_; lean_object* v_vs_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v_ks_3757_ = lean_ctor_get(v_x_3727_, 0);
lean_inc_ref(v_ks_3757_);
v_vs_3758_ = lean_ctor_get(v_x_3727_, 1);
lean_inc_ref(v_vs_3758_);
lean_dec_ref(v_x_3727_);
v___x_3759_ = lean_unsigned_to_nat(0u);
v___x_3760_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3726_, v_ks_3757_, v_vs_3758_, v___x_3759_, v_x_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec_ref(v_vs_3758_);
lean_dec_ref(v_ks_3757_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3761_, lean_object* v_as_3762_, size_t v_i_3763_, size_t v_stop_3764_, lean_object* v_b_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_a_3772_; lean_object* v___y_3777_; uint8_t v___x_3780_; 
v___x_3780_ = lean_usize_dec_eq(v_i_3763_, v_stop_3764_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_array_uget_borrowed(v_as_3762_, v_i_3763_);
switch(lean_obj_tag(v___x_3781_))
{
case 0:
{
lean_object* v_key_3782_; lean_object* v_val_3783_; lean_object* v___x_3784_; 
v_key_3782_ = lean_ctor_get(v___x_3781_, 0);
v_val_3783_ = lean_ctor_get(v___x_3781_, 1);
lean_inc_ref(v_f_3761_);
lean_inc(v___y_3769_);
lean_inc_ref(v___y_3768_);
lean_inc(v___y_3767_);
lean_inc_ref(v___y_3766_);
lean_inc(v_val_3783_);
lean_inc(v_key_3782_);
v___x_3784_ = lean_apply_8(v_f_3761_, v_b_3765_, v_key_3782_, v_val_3783_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, lean_box(0));
v___y_3777_ = v___x_3784_;
goto v___jp_3776_;
}
case 1:
{
lean_object* v_node_3785_; lean_object* v___x_3786_; 
v_node_3785_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_node_3785_);
lean_inc_ref(v_f_3761_);
v___x_3786_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3761_, v_node_3785_, v_b_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
v___y_3777_ = v___x_3786_;
goto v___jp_3776_;
}
default: 
{
v_a_3772_ = v_b_3765_;
goto v___jp_3771_;
}
}
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_dec_ref(v_f_3761_);
v___x_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3787_, 0, v_b_3765_);
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
return v___x_3788_;
}
v___jp_3771_:
{
size_t v___x_3773_; size_t v___x_3774_; 
v___x_3773_ = ((size_t)1ULL);
v___x_3774_ = lean_usize_add(v_i_3763_, v___x_3773_);
v_i_3763_ = v___x_3774_;
v_b_3765_ = v_a_3772_;
goto _start;
}
v___jp_3776_:
{
if (lean_obj_tag(v___y_3777_) == 0)
{
lean_object* v_a_3778_; 
v_a_3778_ = lean_ctor_get(v___y_3777_, 0);
if (lean_obj_tag(v_a_3778_) == 0)
{
lean_dec_ref(v_f_3761_);
return v___y_3777_;
}
else
{
lean_object* v_a_3779_; 
lean_inc_ref(v_a_3778_);
lean_dec_ref(v___y_3777_);
v_a_3779_ = lean_ctor_get(v_a_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v_a_3778_);
v_a_3772_ = v_a_3779_;
goto v___jp_3771_;
}
}
else
{
lean_dec_ref(v_f_3761_);
return v___y_3777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3789_, lean_object* v_as_3790_, lean_object* v_i_3791_, lean_object* v_stop_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
size_t v_i_boxed_3799_; size_t v_stop_boxed_3800_; lean_object* v_res_3801_; 
v_i_boxed_3799_ = lean_unbox_usize(v_i_3791_);
lean_dec(v_i_3791_);
v_stop_boxed_3800_ = lean_unbox_usize(v_stop_3792_);
lean_dec(v_stop_3792_);
v_res_3801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3789_, v_as_3790_, v_i_boxed_3799_, v_stop_boxed_3800_, v_b_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec_ref(v_as_3790_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3802_, lean_object* v_x_3803_, lean_object* v_x_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3802_, v_x_3803_, v_x_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3811_, lean_object* v_s_3812_, lean_object* v_a_3813_, lean_object* v_b_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v_a_3813_);
lean_ctor_set(v___x_3820_, 1, v_b_3814_);
lean_inc(v___y_3818_);
lean_inc_ref(v___y_3817_);
lean_inc(v___y_3816_);
lean_inc_ref(v___y_3815_);
v___x_3821_ = lean_apply_7(v_f_3811_, v___x_3820_, v_s_3812_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, lean_box(0));
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3848_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3848_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3848_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
if (lean_obj_tag(v_a_3822_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3836_; 
v_a_3826_ = lean_ctor_get(v_a_3822_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_a_3822_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3828_ = v_a_3822_;
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v_a_3822_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3833_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3831_);
v___x_3833_ = v___x_3824_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3847_; 
v_a_3837_ = lean_ctor_get(v_a_3822_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_a_3822_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3839_ = v_a_3822_;
v_isShared_3840_ = v_isSharedCheck_3847_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v_a_3822_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3847_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3844_; 
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3842_);
v___x_3844_ = v___x_3824_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3821_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3821_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3857_, lean_object* v_s_3858_, lean_object* v_a_3859_, lean_object* v_b_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3857_, v_s_3858_, v_a_3859_, v_b_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3867_, lean_object* v_init_3868_, lean_object* v_f_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___f_3875_; lean_object* v___x_3876_; 
v___f_3875_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3875_, 0, v_f_3869_);
lean_inc_ref(v_map_3867_);
v___x_3876_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3875_, v_map_3867_, v_init_3868_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3885_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3885_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3885_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v_a_3881_; lean_object* v___x_3883_; 
v_a_3881_ = lean_ctor_get(v_a_3877_, 0);
lean_inc(v_a_3881_);
lean_dec(v_a_3877_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v_a_3881_);
v___x_3883_ = v___x_3879_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3881_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
v_a_3886_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3876_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3876_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3894_, lean_object* v_init_3895_, lean_object* v_f_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3894_, v_init_3895_, v_f_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_map_3894_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; lean_object* v_env_3906_; lean_object* v___x_3907_; lean_object* v_ext_3908_; lean_object* v_toEnvExtension_3909_; lean_object* v_asyncMode_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v_categories_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3905_ = lean_st_ref_get(v___y_3903_);
v_env_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc_ref_n(v_env_3906_, 2);
lean_dec(v___x_3905_);
v___x_3907_ = l_Lean_Parser_parserExtension;
v_ext_3908_ = lean_ctor_get(v___x_3907_, 1);
v_toEnvExtension_3909_ = lean_ctor_get(v_ext_3908_, 0);
v_asyncMode_3910_ = lean_ctor_get(v_toEnvExtension_3909_, 2);
v___x_3911_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3912_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3911_, v___x_3907_, v_env_3906_, v_asyncMode_3910_);
v_categories_3913_ = lean_ctor_get(v___x_3912_, 2);
lean_inc_ref(v_categories_3913_);
lean_dec(v___x_3912_);
v___x_3914_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3915_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3913_, v___x_3914_);
lean_dec_ref(v_categories_3913_);
if (lean_obj_tag(v___x_3915_) == 1)
{
lean_object* v_val_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3953_; 
v_val_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3953_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_val_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3953_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___y_3921_; lean_object* v___x_3930_; lean_object* v_toEnvExtension_3931_; lean_object* v_exportEntriesFn_3932_; lean_object* v_asyncMode_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v_importedEntries_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v_exported_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3930_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3931_ = lean_ctor_get(v___x_3930_, 0);
v_exportEntriesFn_3932_ = lean_ctor_get(v___x_3930_, 4);
v_asyncMode_3933_ = lean_ctor_get(v_toEnvExtension_3931_, 2);
v___x_3934_ = lean_box(1);
v___x_3935_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3936_ = lean_box(0);
lean_inc_ref_n(v_env_3906_, 2);
v___x_3937_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3935_, v_toEnvExtension_3931_, v_env_3906_, v_asyncMode_3933_, v___x_3936_);
v_importedEntries_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc_ref(v_importedEntries_3938_);
lean_dec(v___x_3937_);
v___x_3939_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3934_, v___x_3930_, v_env_3906_, v_asyncMode_3933_, v___x_3936_);
lean_inc_ref(v_exportEntriesFn_3932_);
v___x_3940_ = lean_apply_2(v_exportEntriesFn_3932_, v_env_3906_, v___x_3939_);
v_exported_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_exported_3941_);
lean_dec_ref(v___x_3940_);
v___x_3942_ = lean_array_push(v_importedEntries_3938_, v_exported_3941_);
v___x_3943_ = lean_unsigned_to_nat(0u);
v___x_3944_ = lean_array_get_size(v___x_3942_);
v___x_3945_ = lean_nat_dec_lt(v___x_3943_, v___x_3944_);
if (v___x_3945_ == 0)
{
lean_dec_ref(v___x_3942_);
v___y_3921_ = v___x_3934_;
goto v___jp_3920_;
}
else
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_le(v___x_3944_, v___x_3944_);
if (v___x_3946_ == 0)
{
if (v___x_3945_ == 0)
{
lean_dec_ref(v___x_3942_);
v___y_3921_ = v___x_3934_;
goto v___jp_3920_;
}
else
{
size_t v___x_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = ((size_t)0ULL);
v___x_3948_ = lean_usize_of_nat(v___x_3944_);
v___x_3949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3942_, v___x_3947_, v___x_3948_, v___x_3934_);
lean_dec_ref(v___x_3942_);
v___y_3921_ = v___x_3949_;
goto v___jp_3920_;
}
}
else
{
size_t v___x_3950_; size_t v___x_3951_; lean_object* v___x_3952_; 
v___x_3950_ = ((size_t)0ULL);
v___x_3951_ = lean_usize_of_nat(v___x_3944_);
v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3942_, v___x_3950_, v___x_3951_, v___x_3934_);
lean_dec_ref(v___x_3942_);
v___y_3921_ = v___x_3952_;
goto v___jp_3920_;
}
}
v___jp_3920_:
{
lean_object* v_tables_3922_; lean_object* v_leadingTable_3923_; lean_object* v_trailingTable_3924_; lean_object* v_firstTokens_3925_; lean_object* v_firstTokens_3926_; lean_object* v___x_3928_; 
v_tables_3922_ = lean_ctor_get(v_val_3916_, 2);
v_leadingTable_3923_ = lean_ctor_get(v_tables_3922_, 0);
v_trailingTable_3924_ = lean_ctor_get(v_tables_3922_, 2);
lean_inc(v_trailingTable_3924_);
lean_inc(v_leadingTable_3923_);
lean_inc(v_val_3916_);
v_firstTokens_3925_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3916_, v_leadingTable_3923_, v___y_3921_);
v_firstTokens_3926_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3916_, v_trailingTable_3924_, v_firstTokens_3925_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set_tag(v___x_3918_, 0);
lean_ctor_set(v___x_3918_, 0, v_firstTokens_3926_);
v___x_3928_ = v___x_3918_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_firstTokens_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec(v___x_3915_);
lean_dec_ref(v_env_3906_);
v___x_3954_ = lean_box(1);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3956_);
lean_dec(v___y_3956_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v___x_3967_; lean_object* v_env_3968_; lean_object* v___x_3969_; lean_object* v_toEnvExtension_3970_; lean_object* v_exportEntriesFn_3971_; lean_object* v_asyncMode_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v_importedEntries_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v_exported_3980_; lean_object* v___x_3981_; size_t v_sz_3982_; size_t v___x_3983_; lean_object* v___x_3984_; 
v___x_3967_ = lean_st_ref_get(v_a_3965_);
v_env_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc_ref_n(v_env_3968_, 4);
lean_dec(v___x_3967_);
v___x_3969_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3970_ = lean_ctor_get(v___x_3969_, 0);
v_exportEntriesFn_3971_ = lean_ctor_get(v___x_3969_, 4);
v_asyncMode_3972_ = lean_ctor_get(v_toEnvExtension_3970_, 2);
v___x_3973_ = lean_box(1);
v___x_3974_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3975_ = lean_box(0);
v___x_3976_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3974_, v_toEnvExtension_3970_, v_env_3968_, v_asyncMode_3972_, v___x_3975_);
v_importedEntries_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc_ref(v_importedEntries_3977_);
lean_dec(v___x_3976_);
v___x_3978_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3973_, v___x_3969_, v_env_3968_, v_asyncMode_3972_, v___x_3975_);
lean_inc_ref(v_exportEntriesFn_3971_);
v___x_3979_ = lean_apply_2(v_exportEntriesFn_3971_, v_env_3968_, v___x_3978_);
v_exported_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_exported_3980_);
lean_dec_ref(v___x_3979_);
v___x_3981_ = lean_array_push(v_importedEntries_3977_, v_exported_3980_);
v_sz_3982_ = lean_array_size(v___x_3981_);
v___x_3983_ = ((size_t)0ULL);
v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3981_, v_sz_3982_, v___x_3983_, v___x_3973_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
lean_dec_ref(v___x_3981_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4009_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3987_ = v___x_3984_;
v_isShared_3988_ = v_isSharedCheck_4009_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3984_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4009_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v_ext_3990_; lean_object* v_toEnvExtension_3991_; lean_object* v_asyncMode_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v_categories_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3989_ = l_Lean_Parser_parserExtension;
v_ext_3990_ = lean_ctor_get(v___x_3989_, 1);
v_toEnvExtension_3991_ = lean_ctor_get(v_ext_3990_, 0);
v_asyncMode_3992_ = lean_ctor_get(v_toEnvExtension_3991_, 2);
v___x_3993_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3968_);
v___x_3994_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3993_, v___x_3989_, v_env_3968_, v_asyncMode_3992_);
v_categories_3995_ = lean_ctor_get(v___x_3994_, 2);
lean_inc_ref(v_categories_3995_);
lean_dec(v___x_3994_);
v___x_3996_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3997_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3998_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3995_, v___x_3997_);
lean_dec_ref(v_categories_3995_);
if (lean_obj_tag(v___x_3998_) == 1)
{
lean_object* v_val_3999_; lean_object* v___x_4000_; lean_object* v_a_4001_; lean_object* v_kinds_4002_; lean_object* v___x_4003_; lean_object* v___f_4004_; lean_object* v___x_4005_; 
lean_del_object(v___x_3987_);
v_val_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_val_3999_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3965_);
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v_kinds_4002_ = lean_ctor_get(v_val_3999_, 1);
lean_inc_ref(v_kinds_4002_);
lean_dec(v_val_3999_);
v___x_4003_ = lean_box(v_includeUnnamed_3961_);
v___f_4004_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4004_, 0, v_env_3968_);
lean_closure_set(v___f_4004_, 1, v_a_3985_);
lean_closure_set(v___f_4004_, 2, v_a_4001_);
lean_closure_set(v___f_4004_, 3, v___x_4003_);
v___x_4005_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_4002_, v___x_3996_, v___f_4004_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
lean_dec_ref(v_kinds_4002_);
return v___x_4005_;
}
else
{
lean_object* v___x_4007_; 
lean_dec(v___x_3998_);
lean_dec(v_a_3985_);
lean_dec_ref(v_env_3968_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3996_);
v___x_4007_ = v___x_3987_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3996_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec_ref(v_env_3968_);
v_a_4010_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3984_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3984_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
uint8_t v_includeUnnamed_boxed_4024_; lean_object* v_res_4025_; 
v_includeUnnamed_boxed_4024_ = lean_unbox(v_includeUnnamed_4018_);
v_res_4025_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_4024_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_4026_, size_t v_sz_4027_, size_t v_i_4028_, lean_object* v_b_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4026_, v_sz_4027_, v_i_4028_, v_b_4029_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_4036_, lean_object* v_sz_4037_, lean_object* v_i_4038_, lean_object* v_b_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
size_t v_sz_boxed_4045_; size_t v_i_boxed_4046_; lean_object* v_res_4047_; 
v_sz_boxed_4045_ = lean_unbox_usize(v_sz_4037_);
lean_dec(v_sz_4037_);
v_i_boxed_4046_ = lean_unbox_usize(v_i_4038_);
lean_dec(v_i_4038_);
v_res_4047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_4036_, v_sz_boxed_4045_, v_i_boxed_4046_, v_b_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec_ref(v_as_4036_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4051_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_4060_, lean_object* v_00_u03b2_4061_, lean_object* v_map_4062_, lean_object* v_init_4063_, lean_object* v_f_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4062_, v_init_4063_, v_f_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_4071_, lean_object* v_00_u03b2_4072_, lean_object* v_map_4073_, lean_object* v_init_4074_, lean_object* v_f_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_4071_, v_00_u03b2_4072_, v_map_4073_, v_init_4074_, v_f_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec_ref(v_map_4073_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_4082_, lean_object* v_f_4083_, lean_object* v_init_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4083_, v_map_4082_, v_init_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_4091_, lean_object* v_f_4092_, lean_object* v_init_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_4091_, v_f_4092_, v_init_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
return v_res_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_4100_, lean_object* v_00_u03c3_4101_, lean_object* v_00_u03b2_4102_, lean_object* v_map_4103_, lean_object* v_f_4104_, lean_object* v_init_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4104_, v_map_4103_, v_init_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_4112_, lean_object* v_00_u03c3_4113_, lean_object* v_00_u03b2_4114_, lean_object* v_map_4115_, lean_object* v_f_4116_, lean_object* v_init_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_4112_, v_00_u03c3_4113_, v_00_u03b2_4114_, v_map_4115_, v_f_4116_, v_init_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_4124_, lean_object* v_00_u03c3_4125_, lean_object* v_00_u03b1_4126_, lean_object* v_00_u03b2_4127_, lean_object* v_f_4128_, lean_object* v_x_4129_, lean_object* v_x_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4128_, v_x_4129_, v_x_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_4137_, lean_object* v_00_u03c3_4138_, lean_object* v_00_u03b1_4139_, lean_object* v_00_u03b2_4140_, lean_object* v_f_4141_, lean_object* v_x_4142_, lean_object* v_x_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_4137_, v_00_u03c3_4138_, v_00_u03b1_4139_, v_00_u03b2_4140_, v_f_4141_, v_x_4142_, v_x_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_4150_, lean_object* v_00_u03b2_4151_, lean_object* v_00_u03c3_4152_, lean_object* v_00_u03c3_4153_, lean_object* v_f_4154_, lean_object* v_as_4155_, size_t v_i_4156_, size_t v_stop_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4154_, v_as_4155_, v_i_4156_, v_stop_4157_, v_b_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4165_, lean_object* v_00_u03b2_4166_, lean_object* v_00_u03c3_4167_, lean_object* v_00_u03c3_4168_, lean_object* v_f_4169_, lean_object* v_as_4170_, lean_object* v_i_4171_, lean_object* v_stop_4172_, lean_object* v_b_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
size_t v_i_boxed_4179_; size_t v_stop_boxed_4180_; lean_object* v_res_4181_; 
v_i_boxed_4179_ = lean_unbox_usize(v_i_4171_);
lean_dec(v_i_4171_);
v_stop_boxed_4180_ = lean_unbox_usize(v_stop_4172_);
lean_dec(v_stop_4172_);
v_res_4181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_4165_, v_00_u03b2_4166_, v_00_u03c3_4167_, v_00_u03c3_4168_, v_f_4169_, v_as_4170_, v_i_boxed_4179_, v_stop_boxed_4180_, v_b_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec_ref(v_as_4170_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_4182_, lean_object* v_00_u03c3_4183_, lean_object* v_00_u03b1_4184_, lean_object* v_00_u03b2_4185_, lean_object* v_f_4186_, lean_object* v_keys_4187_, lean_object* v_vals_4188_, lean_object* v_heq_4189_, lean_object* v_i_4190_, lean_object* v_acc_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4186_, v_keys_4187_, v_vals_4188_, v_i_4190_, v_acc_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_4198_, lean_object* v_00_u03c3_4199_, lean_object* v_00_u03b1_4200_, lean_object* v_00_u03b2_4201_, lean_object* v_f_4202_, lean_object* v_keys_4203_, lean_object* v_vals_4204_, lean_object* v_heq_4205_, lean_object* v_i_4206_, lean_object* v_acc_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_4198_, v_00_u03c3_4199_, v_00_u03b1_4200_, v_00_u03b2_4201_, v_f_4202_, v_keys_4203_, v_vals_4204_, v_heq_4205_, v_i_4206_, v_acc_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec_ref(v_vals_4204_);
lean_dec_ref(v_keys_4203_);
return v_res_4213_;
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
