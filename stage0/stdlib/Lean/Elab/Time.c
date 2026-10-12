// Lean compiler output
// Module: Lean.Elab.Time
// Imports: public import Lean.Elab.Command
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__0 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__0_value;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__1 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__1_value;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "timeCmd"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__2 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Time_elabTimeCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 30, 11, 88, 214, 137, 225, 32)}};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__3 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__3_value;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "time: "};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__4 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Time_elabTimeCmd___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__5;
static const lean_string_object l_Lean_Elab_Time_elabTimeCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ms"};
static const lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__6 = (const lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Time_elabTimeCmd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Time_elabTimeCmd___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Time"};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabTimeCmd"};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Time_elabTimeCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 109, 103, 22, 229, 14, 107, 103)}};
static const lean_ctor_object l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 103, 203, 174, 210, 209, 148, 47)}};
static const lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(lean_box(0), v___y_11_, v___y_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object* v_00_u03b1_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(v_00_u03b1_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_20_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_22_, uint8_t v___y_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 1)
{
lean_object* v_pre_25_; 
v_pre_25_ = lean_ctor_get(v_x_24_, 0);
if (lean_obj_tag(v_pre_25_) == 0)
{
lean_object* v_str_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_str_26_ = lean_ctor_get(v_x_24_, 1);
v___x_27_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0));
v___x_28_ = lean_string_dec_eq(v_str_26_, v___x_27_);
if (v___x_28_ == 0)
{
return v___x_28_;
}
else
{
return v_suppressElabErrors_22_;
}
}
else
{
return v___y_23_;
}
}
else
{
return v___y_23_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_22_ = stack[0].m_num;
uint8_t v___y_23_ = stack[1].m_num;
lean_object* v_x_24_ = stack[2].m_obj;
uint8_t v_res_29_;
v_res_29_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(v_suppressElabErrors_22_, v___y_23_, v_x_24_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_30_, lean_object* v___y_31_, lean_object* v_x_32_){
_start:
{
uint8_t v_suppressElabErrors_boxed_33_; uint8_t v___y_2746__boxed_34_; uint8_t v_res_35_; lean_object* v_r_36_; 
v_suppressElabErrors_boxed_33_ = lean_unbox(v_suppressElabErrors_30_);
v___y_2746__boxed_34_ = lean_unbox(v___y_31_);
v_res_35_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_33_, v___y_2746__boxed_34_, v_x_32_);
lean_dec(v_x_32_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(lean_object* v_opts_37_, lean_object* v_opt_38_){
_start:
{
lean_object* v_name_39_; lean_object* v_defValue_40_; lean_object* v_map_41_; lean_object* v___x_42_; 
v_name_39_ = lean_ctor_get(v_opt_38_, 0);
v_defValue_40_ = lean_ctor_get(v_opt_38_, 1);
v_map_41_ = lean_ctor_get(v_opts_37_, 0);
v___x_42_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_41_, v_name_39_);
if (lean_obj_tag(v___x_42_) == 0)
{
uint8_t v___x_43_; 
v___x_43_ = lean_unbox(v_defValue_40_);
return v___x_43_;
}
else
{
lean_object* v_val_44_; 
v_val_44_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v___x_42_, 1);
if (lean_obj_tag(v_val_44_) == 1)
{
uint8_t v_v_45_; 
v_v_45_ = lean_ctor_get_uint8(v_val_44_, 0);
lean_dec_ref_known(v_val_44_, 0);
return v_v_45_;
}
else
{
uint8_t v___x_46_; 
lean_dec(v_val_44_);
v___x_46_ = lean_unbox(v_defValue_40_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_37_ = stack[0].m_obj;
lean_object* v_opt_38_ = stack[1].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_37_, v_opt_38_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_48_, lean_object* v_opt_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_48_, v_opt_49_);
lean_dec_ref(v_opt_49_);
lean_dec_ref(v_opts_48_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_52_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_56_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
lean_ctor_set(v___x_58_, 2, v___x_57_);
lean_ctor_set(v___x_58_, 3, v___x_57_);
lean_ctor_set(v___x_58_, 4, v___x_56_);
lean_ctor_set(v___x_58_, 5, v___x_56_);
lean_ctor_set(v___x_58_, 6, v___x_56_);
lean_ctor_set(v___x_58_, 7, v___x_56_);
lean_ctor_set(v___x_58_, 8, v___x_56_);
lean_ctor_set(v___x_58_, 9, v___x_56_);
lean_ctor_set(v___x_58_, 10, v___x_56_);
lean_ctor_set(v___x_58_, 11, v___x_55_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_unsigned_to_nat(32u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_62_ = ((size_t)5ULL);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_unsigned_to_nat(32u);
v___x_65_ = lean_mk_empty_array_with_capacity(v___x_64_);
v___x_66_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_67_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_63_);
lean_ctor_set(v___x_67_, 3, v___x_63_);
lean_ctor_set_usize(v___x_67_, 4, v___x_62_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_box(1);
v___x_69_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_70_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_env_76_; uint8_t v___x_77_; lean_object* v_env_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_scopes_81_; lean_object* v___x_82_; lean_object* v_opts_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = 0;
v_env_78_ = l_Lean_Environment_setRecordingDeps(v_env_76_, v___x_77_);
v___x_79_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_80_ = lean_st_ref_get(v___y_73_);
v_scopes_81_ = lean_ctor_get(v___x_80_, 2);
lean_inc(v_scopes_81_);
lean_dec(v___x_80_);
v___x_82_ = l_List_head_x21___redArg(v___x_79_, v_scopes_81_);
lean_dec(v_scopes_81_);
v_opts_83_ = lean_ctor_get(v___x_82_, 1);
lean_inc_ref(v_opts_83_);
lean_dec(v___x_82_);
v___x_84_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_85_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5);
v___x_86_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_86_, 0, v_env_78_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_85_);
lean_ctor_set(v___x_86_, 3, v_opts_83_);
v___x_87_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_msgData_72_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_72_ = stack[0].m_obj;
lean_object* v___y_73_ = stack[1].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_72_, v___y_73_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_90_, v___y_91_);
lean_dec(v___y_91_);
return v_res_93_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(lean_object* v_ref_95_, lean_object* v_msgData_96_, uint8_t v_severity_97_, uint8_t v_isSilent_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; uint8_t v___y_106_; uint8_t v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; uint8_t v___y_168_; lean_object* v___y_169_; uint8_t v___y_170_; uint8_t v___y_171_; lean_object* v___y_172_; uint8_t v___y_196_; lean_object* v___y_197_; uint8_t v___y_198_; uint8_t v___y_199_; lean_object* v___y_200_; uint8_t v___y_204_; uint8_t v___y_205_; uint8_t v___y_206_; uint8_t v___x_221_; uint8_t v___y_223_; uint8_t v___y_224_; uint8_t v___y_225_; uint8_t v___y_227_; uint8_t v___x_239_; 
v___x_221_ = 2;
v___x_239_ = l_Lean_instBEqMessageSeverity_beq(v_severity_97_, v___x_221_);
if (v___x_239_ == 0)
{
v___y_227_ = v___x_239_;
goto v___jp_226_;
}
else
{
uint8_t v___x_240_; 
lean_inc_ref(v_msgData_96_);
v___x_240_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_96_);
v___y_227_ = v___x_240_;
goto v___jp_226_;
}
v___jp_102_:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Elab_Command_getScope___redArg(v___y_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v_currNamespace_113_; lean_object* v___x_114_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v_currNamespace_113_ = lean_ctor_get(v_a_112_, 2);
lean_inc(v_currNamespace_113_);
lean_dec(v_a_112_);
v___x_114_ = l_Lean_Elab_Command_getScope___redArg(v___y_110_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_150_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_150_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_150_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_150_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_openDecls_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_env_124_; lean_object* v_messages_125_; lean_object* v_scopes_126_; lean_object* v_usedQuotCtxts_127_; lean_object* v_nextMacroScope_128_; lean_object* v_maxRecDepth_129_; lean_object* v_ngen_130_; lean_object* v_auxDeclNGen_131_; lean_object* v_infoState_132_; lean_object* v_traceState_133_; lean_object* v_snapshotTasks_134_; lean_object* v_prevLinterStates_135_; lean_object* v_codeQualityEntryTasks_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_149_; 
v_openDecls_119_ = lean_ctor_get(v_a_115_, 3);
lean_inc(v_openDecls_119_);
lean_dec(v_a_115_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_currNamespace_113_);
lean_ctor_set(v___x_120_, 1, v_openDecls_119_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___y_109_);
lean_inc_ref(v___y_104_);
lean_inc_ref(v___y_108_);
v___x_122_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_122_, 0, v___y_108_);
lean_ctor_set(v___x_122_, 1, v___y_103_);
lean_ctor_set(v___x_122_, 2, v___y_105_);
lean_ctor_set(v___x_122_, 3, v___y_104_);
lean_ctor_set(v___x_122_, 4, v___x_121_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*5, v___y_107_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*5 + 1, v___y_106_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*5 + 2, v_isSilent_98_);
v___x_123_ = lean_st_ref_take(v___y_110_);
v_env_124_ = lean_ctor_get(v___x_123_, 0);
v_messages_125_ = lean_ctor_get(v___x_123_, 1);
v_scopes_126_ = lean_ctor_get(v___x_123_, 2);
v_usedQuotCtxts_127_ = lean_ctor_get(v___x_123_, 3);
v_nextMacroScope_128_ = lean_ctor_get(v___x_123_, 4);
v_maxRecDepth_129_ = lean_ctor_get(v___x_123_, 5);
v_ngen_130_ = lean_ctor_get(v___x_123_, 6);
v_auxDeclNGen_131_ = lean_ctor_get(v___x_123_, 7);
v_infoState_132_ = lean_ctor_get(v___x_123_, 8);
v_traceState_133_ = lean_ctor_get(v___x_123_, 9);
v_snapshotTasks_134_ = lean_ctor_get(v___x_123_, 10);
v_prevLinterStates_135_ = lean_ctor_get(v___x_123_, 11);
v_codeQualityEntryTasks_136_ = lean_ctor_get(v___x_123_, 12);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_149_ == 0)
{
v___x_138_ = v___x_123_;
v_isShared_139_ = v_isSharedCheck_149_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_codeQualityEntryTasks_136_);
lean_inc(v_prevLinterStates_135_);
lean_inc(v_snapshotTasks_134_);
lean_inc(v_traceState_133_);
lean_inc(v_infoState_132_);
lean_inc(v_auxDeclNGen_131_);
lean_inc(v_ngen_130_);
lean_inc(v_maxRecDepth_129_);
lean_inc(v_nextMacroScope_128_);
lean_inc(v_usedQuotCtxts_127_);
lean_inc(v_scopes_126_);
lean_inc(v_messages_125_);
lean_inc(v_env_124_);
lean_dec(v___x_123_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_149_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_box(0);
v___x_141_ = l_Lean_MessageLog_add(v___x_122_, v_messages_125_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_env_124_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_scopes_126_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_usedQuotCtxts_127_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_nextMacroScope_128_);
lean_ctor_set(v_reuseFailAlloc_148_, 5, v_maxRecDepth_129_);
lean_ctor_set(v_reuseFailAlloc_148_, 6, v_ngen_130_);
lean_ctor_set(v_reuseFailAlloc_148_, 7, v_auxDeclNGen_131_);
lean_ctor_set(v_reuseFailAlloc_148_, 8, v_infoState_132_);
lean_ctor_set(v_reuseFailAlloc_148_, 9, v_traceState_133_);
lean_ctor_set(v_reuseFailAlloc_148_, 10, v_snapshotTasks_134_);
lean_ctor_set(v_reuseFailAlloc_148_, 11, v_prevLinterStates_135_);
lean_ctor_set(v_reuseFailAlloc_148_, 12, v_codeQualityEntryTasks_136_);
v___x_143_ = v_reuseFailAlloc_148_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_st_ref_put(v___y_110_, v___x_143_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_140_);
v___x_146_ = v___x_117_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_140_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_currNamespace_113_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_103_);
v_a_151_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_114_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_114_);
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
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v___y_109_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_103_);
v_a_159_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_111_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_111_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
v___jp_167_:
{
lean_object* v_fileName_173_; lean_object* v_fileMap_174_; uint8_t v_suppressElabErrors_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_194_; 
v_fileName_173_ = lean_ctor_get(v___y_99_, 0);
v_fileMap_174_ = lean_ctor_get(v___y_99_, 1);
v_suppressElabErrors_175_ = lean_ctor_get_uint8(v___y_99_, sizeof(void*)*10);
v___x_176_ = lean_box(v_suppressElabErrors_175_);
v___x_177_ = lean_box(v___y_168_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_178_, 0, v___x_176_);
lean_closure_set(v___f_178_, 1, v___x_177_);
v___x_179_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_96_);
v___x_180_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v___x_179_, v___y_100_);
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_194_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc_ref_n(v_fileMap_174_, 2);
v___x_185_ = l_Lean_FileMap_toPosition(v_fileMap_174_, v___y_169_);
lean_dec(v___y_169_);
v___x_186_ = l_Lean_FileMap_toPosition(v_fileMap_174_, v___y_172_);
lean_dec(v___y_172_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0));
if (v_suppressElabErrors_175_ == 0)
{
lean_del_object(v___x_183_);
lean_dec_ref(v___f_178_);
v___y_103_ = v___x_185_;
v___y_104_ = v___x_188_;
v___y_105_ = v___x_187_;
v___y_106_ = v___y_170_;
v___y_107_ = v___y_171_;
v___y_108_ = v_fileName_173_;
v___y_109_ = v_a_181_;
v___y_110_ = v___y_100_;
goto v___jp_102_;
}
else
{
uint8_t v___x_189_; 
lean_inc(v_a_181_);
v___x_189_ = l_Lean_MessageData_hasTag(v___f_178_, v_a_181_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec_ref_known(v___x_187_, 1);
lean_dec_ref(v___x_185_);
lean_dec(v_a_181_);
v___x_190_ = lean_box(0);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_190_);
v___x_192_ = v___x_183_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_del_object(v___x_183_);
v___y_103_ = v___x_185_;
v___y_104_ = v___x_188_;
v___y_105_ = v___x_187_;
v___y_106_ = v___y_170_;
v___y_107_ = v___y_171_;
v___y_108_ = v_fileName_173_;
v___y_109_ = v_a_181_;
v___y_110_ = v___y_100_;
goto v___jp_102_;
}
}
}
}
v___jp_195_:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Syntax_getTailPos_x3f(v___y_197_, v___y_199_);
lean_dec(v___y_197_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_inc(v___y_200_);
v___y_168_ = v___y_196_;
v___y_169_ = v___y_200_;
v___y_170_ = v___y_198_;
v___y_171_ = v___y_199_;
v___y_172_ = v___y_200_;
goto v___jp_167_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_201_, 1);
v___y_168_ = v___y_196_;
v___y_169_ = v___y_200_;
v___y_170_ = v___y_198_;
v___y_171_ = v___y_199_;
v___y_172_ = v_val_202_;
goto v___jp_167_;
}
}
v___jp_203_:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Elab_Command_getRef___redArg(v___y_99_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_ref_209_; lean_object* v___x_210_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v_ref_209_ = l_Lean_replaceRef(v_ref_95_, v_a_208_);
lean_dec(v_a_208_);
v___x_210_ = l_Lean_Syntax_getPos_x3f(v_ref_209_, v___y_205_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___y_196_ = v___y_204_;
v___y_197_ = v_ref_209_;
v___y_198_ = v___y_206_;
v___y_199_ = v___y_205_;
v___y_200_ = v___x_211_;
goto v___jp_195_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
v___y_196_ = v___y_204_;
v___y_197_ = v_ref_209_;
v___y_198_ = v___y_206_;
v___y_199_ = v___y_205_;
v___y_200_ = v_val_212_;
goto v___jp_195_;
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_msgData_96_);
v_a_213_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_207_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_207_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
v___jp_222_:
{
if (v___y_225_ == 0)
{
v___y_204_ = v___y_223_;
v___y_205_ = v___y_224_;
v___y_206_ = v_severity_97_;
goto v___jp_203_;
}
else
{
v___y_204_ = v___y_223_;
v___y_205_ = v___y_224_;
v___y_206_ = v___x_221_;
goto v___jp_203_;
}
}
v___jp_226_:
{
if (v___y_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_scopes_230_; lean_object* v___x_231_; lean_object* v_opts_232_; uint8_t v___x_233_; uint8_t v___x_234_; 
v___x_228_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_229_ = lean_st_ref_get(v___y_100_);
v_scopes_230_ = lean_ctor_get(v___x_229_, 2);
lean_inc(v_scopes_230_);
lean_dec(v___x_229_);
v___x_231_ = l_List_head_x21___redArg(v___x_228_, v_scopes_230_);
lean_dec(v_scopes_230_);
v_opts_232_ = lean_ctor_get(v___x_231_, 1);
lean_inc_ref(v_opts_232_);
lean_dec(v___x_231_);
v___x_233_ = 1;
v___x_234_ = l_Lean_instBEqMessageSeverity_beq(v_severity_97_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v_opts_232_);
v___y_223_ = v___y_227_;
v___y_224_ = v___y_227_;
v___y_225_ = v___x_234_;
goto v___jp_222_;
}
else
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = l_Lean_warningAsError;
v___x_236_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_232_, v___x_235_);
lean_dec_ref(v_opts_232_);
v___y_223_ = v___y_227_;
v___y_224_ = v___y_227_;
v___y_225_ = v___x_236_;
goto v___jp_222_;
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v_msgData_96_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_95_ = stack[0].m_obj;
lean_object* v_msgData_96_ = stack[1].m_obj;
uint8_t v_severity_97_ = stack[2].m_num;
uint8_t v_isSilent_98_ = stack[3].m_num;
lean_object* v___y_99_ = stack[4].m_obj;
lean_object* v___y_100_ = stack[5].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_95_, v_msgData_96_, v_severity_97_, v_isSilent_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___boxed(lean_object* v_ref_242_, lean_object* v_msgData_243_, lean_object* v_severity_244_, lean_object* v_isSilent_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
uint8_t v_severity_boxed_249_; uint8_t v_isSilent_boxed_250_; lean_object* v_res_251_; 
v_severity_boxed_249_ = lean_unbox(v_severity_244_);
v_isSilent_boxed_250_ = lean_unbox(v_isSilent_245_);
v_res_251_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_242_, v_msgData_243_, v_severity_boxed_249_, v_isSilent_boxed_250_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v_ref_242_);
return v_res_251_;
}
}
lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(lean_object* v_ref_252_, lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_257_ = 0;
v___x_258_ = 0;
v___x_259_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(v_ref_252_, v_msgData_253_, v___x_257_, v___x_258_, v___y_254_, v___y_255_);
return v___x_259_;
}
}
LEAN_EXPORT void l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_252_ = stack[0].m_obj;
lean_object* v_msgData_253_ = stack[1].m_obj;
lean_object* v___y_254_ = stack[2].m_obj;
lean_object* v___y_255_ = stack[3].m_obj;
lean_object* v_res_260_;
v_res_260_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_ref_252_, v_msgData_253_, v___y_254_, v___y_255_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1___boxed(lean_object* v_ref_261_, lean_object* v_msgData_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_ref_261_, v_msgData_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v_ref_261_);
return v_res_266_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__5(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__4));
v___x_276_ = l_Lean_stringToMessageData(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Elab_Time_elabTimeCmd___closed__7(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__6));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object* v_x_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
lean_inc(v_x_280_);
v___x_285_ = l_Lean_Syntax_isOfKind(v_x_280_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec(v_x_280_);
v___x_286_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v_tk_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v_tk_288_ = l_Lean_Syntax_getArg(v_x_280_, v___x_287_);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = l_Lean_Syntax_getArg(v_x_280_, v___x_289_);
lean_dec(v_x_280_);
v___x_291_ = lean_io_mono_ms_now();
v___x_292_ = l_Lean_Elab_Command_elabCommand(v___x_290_, v_a_281_, v_a_282_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_308_; 
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_292_, 0);
lean_dec(v_unused_309_);
v___x_294_ = v___x_292_;
v_isShared_295_ = v_isSharedCheck_308_;
goto v_resetjp_293_;
}
else
{
lean_dec(v___x_292_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_308_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_296_ = lean_io_mono_ms_now();
v___x_297_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__5, &l_Lean_Elab_Time_elabTimeCmd___closed__5_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__5);
v___x_298_ = lean_nat_sub(v___x_296_, v___x_291_);
lean_dec(v___x_291_);
lean_dec(v___x_296_);
v___x_299_ = l_Nat_reprFast(v___x_298_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 3);
lean_ctor_set(v___x_294_, 0, v___x_299_);
v___x_301_ = v___x_294_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_307_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_302_ = l_Lean_MessageData_ofFormat(v___x_301_);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_297_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_obj_once(&l_Lean_Elab_Time_elabTimeCmd___closed__7, &l_Lean_Elab_Time_elabTimeCmd___closed__7_once, _init_l_Lean_Elab_Time_elabTimeCmd___closed__7);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(v_tk_288_, v___x_305_, v_a_281_, v_a_282_);
lean_dec(v_tk_288_);
return v___x_306_;
}
}
}
else
{
lean_dec(v___x_291_);
lean_dec(v_tk_288_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Time_elabTimeCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_280_ = stack[0].m_obj;
lean_object* v_a_281_ = stack[1].m_obj;
lean_object* v_a_282_ = stack[2].m_obj;
lean_object* v_res_310_;
v_res_310_ = l_Lean_Elab_Time_elabTimeCmd(v_x_280_, v_a_281_, v_a_282_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd___boxed(lean_object* v_x_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Elab_Time_elabTimeCmd(v_x_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_315_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_316_, v___y_318_);
return v___x_320_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_316_ = stack[0].m_obj;
lean_object* v___y_317_ = stack[1].m_obj;
lean_object* v___y_318_ = stack[2].m_obj;
lean_object* v_res_321_;
v_res_321_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(v_msgData_316_, v___y_317_, v___y_318_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(v_msgData_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_326_;
}
}
lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_336_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_337_ = ((lean_object*)(l_Lean_Elab_Time_elabTimeCmd___closed__3));
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3));
v___x_339_ = lean_alloc_closure((void*)(l_Lean_Elab_Time_elabTimeCmd___boxed), 4, 0);
v___x_340_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_336_, v___x_337_, v___x_338_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_341_;
v_res_341_ = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___boxed(lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
return v_res_343_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Time(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Time(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Time(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Time(builtin);
}
#ifdef __cplusplus
}
#endif
