/*
 * This file is part of the Green library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */

/**
 * Provides the three core classes that are used throughout the rest of the
 * GREEN system.
 * 
 * <ul>
 * 
 * <li>{@link za.ac.sun.cs.green.Green} represents one instantiation of the
 * solver. It can serve multiple clients with multiple clients and solve
 * multiple problems, but it maintains its own unique configuration and
 * in-memory caches and stores.</li>
 *
 * <li>{@link za.ac.sun.cs.green.Instance} represents one problem presented to
 * Green to solve. An instance can be self-contained or it can form the last
 * link in a chain of instances which are combined when it is solved. Some
 * services can exploit this latter scenario to avoid redoing unnecessary
 * work.</li>
 * 
 * <li>{@link za.ac.sun.cs.green.Service} is an interface that forms the basis
 * for all the services provided by a GREEN solver instance. Services are
 * organized in a tree-like structure described by the system configuration.
 * Some services are terminal (such as an SMT solver) while others perform
 * internal processing.</li>
 * 
 * </ul>
 */

package za.ac.sun.cs.green;
