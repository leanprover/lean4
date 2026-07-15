// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: public import Lean.Exception
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getName(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "postpone"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 147, 226, 184, 25, 148, 1, 197)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_postponeExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unsupportedSyntax"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 51, 203, 242, 163, 164, 191, 80)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "abortCommandElab"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 77, 82, 173, 197, 44, 118, 60)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortCommandExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "abortTermElab"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 148, 87, 84, 76, 250, 173, 131)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortTermExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "abortTactic"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 196, 8, 94, 141, 48, 206, 206)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortTacticExceptionId;
static const lean_string_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "autoBoundImplicit"};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 126, 94, 243, 65, 39, 77, 227)}};
static const lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_autoBoundImplicitExceptionId;
static lean_once_cell_t l_Lean_Elab_throwPostpone___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwPostpone___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ill-formed syntax"};
static const lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "localId"};
static const lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 23, 246, 250, 79, 174, 148, 42)}};
static const lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "a universe level named `"};
static const lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1;
static const lean_string_object l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTactic___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTactic___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortTacticException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortException___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_mkMessageCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_mkMessageCore___closed__0 = (const lean_object*)&l_Lean_Elab_mkMessageCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_));
v___x_6_ = l_Lean_registerInternalExceptionId(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_));
v___x_14_ = l_Lean_registerInternalExceptionId(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2____boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_));
v___x_22_ = l_Lean_registerInternalExceptionId(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2____boxed(lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_));
v___x_30_ = l_Lean_registerInternalExceptionId(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2____boxed(lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_));
v___x_38_ = l_Lean_registerInternalExceptionId(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2____boxed(lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = ((lean_object*)(l___private_Lean_Elab_Exception_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_));
v___x_46_ = l_Lean_registerInternalExceptionId(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2____boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
return v_res_48_;
}
}
static lean_object* _init_l_Lean_Elab_throwPostpone___redArg___closed__0(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_box(0);
v___x_50_ = l_Lean_Elab_postponeExceptionId;
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object* v_inst_52_){
_start:
{
lean_object* v_throw_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_throw_53_ = lean_ctor_get(v_inst_52_, 0);
lean_inc(v_throw_53_);
lean_dec_ref(v_inst_52_);
v___x_54_ = lean_obj_once(&l_Lean_Elab_throwPostpone___redArg___closed__0, &l_Lean_Elab_throwPostpone___redArg___closed__0_once, _init_l_Lean_Elab_throwPostpone___redArg___closed__0);
v___x_55_ = lean_apply_2(v_throw_53_, lean_box(0), v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object* v_m_56_, lean_object* v_00_u03b1_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Elab_throwPostpone___redArg(v_inst_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object* v_inst_63_){
_start:
{
lean_object* v_throw_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_throw_64_ = lean_ctor_get(v_inst_63_, 0);
lean_inc(v_throw_64_);
lean_dec_ref(v_inst_63_);
v___x_65_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0);
v___x_66_ = lean_apply_2(v_throw_64_, lean_box(0), v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object* v_m_67_, lean_object* v_00_u03b1_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v_inst_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0));
v___x_73_ = l_Lean_stringToMessageData(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object* v_inst_74_, lean_object* v_inst_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1, &l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1_once, _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1);
v___x_77_ = l_Lean_throwError___redArg(v_inst_74_, v_inst_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object* v_m_78_, lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Elab_throwIllFormedSyntax___redArg(v_inst_80_, v_inst_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object* v_inst_86_, lean_object* v_n_87_){
_start:
{
lean_object* v_throw_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_101_; 
v_throw_88_ = lean_ctor_get(v_inst_86_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_inst_86_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; 
v_unused_102_ = lean_ctor_get(v_inst_86_, 1);
lean_dec(v_unused_102_);
v___x_90_ = v_inst_86_;
v_isShared_91_ = v_isSharedCheck_101_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_throw_88_);
lean_dec(v_inst_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_101_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_92_ = l_Lean_Elab_autoBoundImplicitExceptionId;
v___x_93_ = l_Lean_KVMap_empty;
v___x_94_ = ((lean_object*)(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1));
v___x_95_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_95_, 0, v_n_87_);
v___x_96_ = l_Lean_KVMap_insert(v___x_93_, v___x_94_, v___x_95_);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 1);
lean_ctor_set(v___x_90_, 1, v___x_96_);
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_98_ = v___x_90_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_100_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; 
v___x_99_ = lean_apply_2(v_throw_88_, lean_box(0), v___x_98_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object* v_m_103_, lean_object* v_00_u03b1_104_, lean_object* v_inst_105_, lean_object* v_n_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(v_inst_105_, v_n_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object* v_ex_111_){
_start:
{
if (lean_obj_tag(v_ex_111_) == 1)
{
lean_object* v_id_112_; lean_object* v_extra_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_id_112_ = lean_ctor_get(v_ex_111_, 0);
v_extra_113_ = lean_ctor_get(v_ex_111_, 1);
v___x_114_ = l_Lean_Elab_autoBoundImplicitExceptionId;
v___x_115_ = l_Lean_instBEqInternalExceptionId_beq(v_id_112_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1));
v___x_118_ = ((lean_object*)(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1));
v___x_119_ = l_Lean_KVMap_getName(v_extra_113_, v___x_117_, v___x_118_);
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
else
{
lean_object* v___x_121_; 
v___x_121_ = lean_box(0);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object* v_ex_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(v_ex_122_);
lean_dec_ref(v_ex_122_);
return v_res_123_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0));
v___x_126_ = l_Lean_stringToMessageData(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2));
v___x_129_ = l_Lean_stringToMessageData(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_u_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_133_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1);
v___x_134_ = l_Lean_MessageData_ofName(v_u_132_);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_obj_once(&l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3, &l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3_once, _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3);
v___x_137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = l_Lean_throwError___redArg(v_inst_130_, v_inst_131_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object* v_m_139_, lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_u_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(v_inst_141_, v_inst_142_, v_u_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_box(0);
v___x_146_ = l_Lean_Elab_abortCommandExceptionId;
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object* v_inst_148_){
_start:
{
lean_object* v_throw_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_throw_149_ = lean_ctor_get(v_inst_148_, 0);
lean_inc(v_throw_149_);
lean_dec_ref(v_inst_148_);
v___x_150_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0);
v___x_151_ = lean_apply_2(v_throw_149_, lean_box(0), v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object* v_00_u03b1_152_, lean_object* v_m_153_, lean_object* v_inst_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Elab_throwAbortCommand___redArg(v_inst_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = l_Lean_Elab_abortTermExceptionId;
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object* v_inst_159_){
_start:
{
lean_object* v_throw_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_throw_160_ = lean_ctor_get(v_inst_159_, 0);
lean_inc(v_throw_160_);
lean_dec_ref(v_inst_159_);
v___x_161_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0);
v___x_162_ = lean_apply_2(v_throw_160_, lean_box(0), v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object* v_00_u03b1_163_, lean_object* v_m_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Elab_throwAbortTerm___redArg(v_inst_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(0);
v___x_168_ = l_Lean_Elab_abortTacticExceptionId;
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object* v_inst_170_){
_start:
{
lean_object* v_throw_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_throw_171_ = lean_ctor_get(v_inst_170_, 0);
lean_inc(v_throw_171_);
lean_dec_ref(v_inst_170_);
v___x_172_ = lean_obj_once(&l_Lean_Elab_throwAbortTactic___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0);
v___x_173_ = lean_apply_2(v_throw_171_, lean_box(0), v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object* v_00_u03b1_174_, lean_object* v_m_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Elab_throwAbortTactic___redArg(v_inst_176_);
return v___x_177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortTacticException(lean_object* v_ex_178_){
_start:
{
if (lean_obj_tag(v_ex_178_) == 1)
{
lean_object* v_id_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_id_179_ = lean_ctor_get(v_ex_178_, 0);
v___x_180_ = l_Lean_Elab_abortTacticExceptionId;
v___x_181_ = l_Lean_instBEqInternalExceptionId_beq(v_id_179_, v___x_180_);
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object* v_ex_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Lean_Elab_isAbortTacticException(v_ex_183_);
lean_dec_ref(v_ex_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortExceptionId(lean_object* v_id_186_){
_start:
{
uint8_t v___y_188_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = l_Lean_Elab_abortCommandExceptionId;
v___x_192_ = l_Lean_instBEqInternalExceptionId_beq(v_id_186_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = l_Lean_Elab_abortTermExceptionId;
v___x_194_ = l_Lean_instBEqInternalExceptionId_beq(v_id_186_, v___x_193_);
v___y_188_ = v___x_194_;
goto v___jp_187_;
}
else
{
v___y_188_ = v___x_192_;
goto v___jp_187_;
}
v___jp_187_:
{
if (v___y_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = l_Lean_Elab_abortTacticExceptionId;
v___x_190_ = l_Lean_instBEqInternalExceptionId_beq(v_id_186_, v___x_189_);
return v___x_190_;
}
else
{
return v___y_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object* v_id_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Lean_Elab_isAbortExceptionId(v_id_195_);
lean_dec(v_id_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortException(lean_object* v_ex_198_){
_start:
{
if (lean_obj_tag(v_ex_198_) == 1)
{
lean_object* v_id_199_; uint8_t v___x_200_; 
v_id_199_ = lean_ctor_get(v_ex_198_, 0);
v___x_200_ = l_Lean_Elab_isAbortExceptionId(v_id_199_);
return v___x_200_;
}
else
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortException___boxed(lean_object* v_ex_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Elab_isAbortException(v_ex_202_);
lean_dec_ref(v_ex_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore(lean_object* v_fileName_206_, lean_object* v_fileMap_207_, lean_object* v_data_208_, uint8_t v_severity_209_, lean_object* v_pos_210_, lean_object* v_endPos_211_){
_start:
{
lean_object* v_pos_212_; lean_object* v_endPos_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
lean_inc_ref(v_fileMap_207_);
v_pos_212_ = l_Lean_FileMap_toPosition(v_fileMap_207_, v_pos_210_);
v_endPos_213_ = l_Lean_FileMap_toPosition(v_fileMap_207_, v_endPos_211_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_endPos_213_);
v___x_215_ = 0;
v___x_216_ = ((lean_object*)(l_Lean_Elab_mkMessageCore___closed__0));
v___x_217_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_217_, 0, v_fileName_206_);
lean_ctor_set(v___x_217_, 1, v_pos_212_);
lean_ctor_set(v___x_217_, 2, v___x_214_);
lean_ctor_set(v___x_217_, 3, v___x_216_);
lean_ctor_set(v___x_217_, 4, v_data_208_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*5, v___x_215_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*5 + 1, v_severity_209_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*5 + 2, v___x_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object* v_fileName_218_, lean_object* v_fileMap_219_, lean_object* v_data_220_, lean_object* v_severity_221_, lean_object* v_pos_222_, lean_object* v_endPos_223_){
_start:
{
uint8_t v_severity_boxed_224_; lean_object* v_res_225_; 
v_severity_boxed_224_ = lean_unbox(v_severity_221_);
v_res_225_ = l_Lean_Elab_mkMessageCore(v_fileName_218_, v_fileMap_219_, v_data_220_, v_severity_boxed_224_, v_pos_222_, v_endPos_223_);
lean_dec(v_endPos_223_);
lean_dec(v_pos_222_);
return v_res_225_;
}
}
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Exception(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_postponeExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_postponeExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_unsupportedSyntaxExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_unsupportedSyntaxExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortCommandExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortCommandExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTermExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTermExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTacticExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTacticExceptionId);
lean_dec_ref(res);
res = l___private_Lean_Elab_Exception_0__Lean_Elab_initFn_00___x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoBoundImplicitExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoBoundImplicitExceptionId);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Exception(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Exception(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Exception(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Exception(builtin);
}
#ifdef __cplusplus
}
#endif
