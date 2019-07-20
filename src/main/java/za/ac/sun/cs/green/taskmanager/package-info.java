/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */

/**
 * Task managers take care of executing an instance for a GREEN service, which
 * is in fact a tree of services. This requires careful management because each
 * such execution consists of three repeated method calls:
 * 
 * <ul>
 * <li>{@link za.ac.sun.cs.green.Service#processRequest(za.ac.sun.cs.green.Instance)}</li>
 * <li>{@link za.ac.sun.cs.green.Service#childDone(za.ac.sun.cs.green.Instance, za.ac.sun.cs.green.Service, za.ac.sun.cs.green.Instance, Object)}</li>
 * <li>{@link za.ac.sun.cs.green.Service#allChildrenDone(za.ac.sun.cs.green.Instance, Object)}</li>
 * </ul>
 * 
 * Each service in the tree can have multiple child services and each
 * {@code processRequiest()} invocation may spawn several child instances. It is
 * important that the calls happen in the right order, taking into account
 * special circumstances, and that the return values are passed to the right
 * place in the right order.
 */

package za.ac.sun.cs.green.taskmanager;
