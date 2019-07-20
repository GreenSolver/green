/*
 * This file is part of the GREEN library, https://greensolver.github.io/green/
 *
 * Copyright (c) 2019, Computer Science, Stellenbosch University.  All rights reserved.
 *
 * Licensed under GNU Lesser General Public License, version 3.
 * See LICENSE.md file in the project root for full license information.
 */

/**
 * The renaming service simply renames the variables in an expression. At
 * present, it does not name the variables back at the end of the computation,
 * so the only reasonable application is to rename expression for a SAT or
 * counting query in the case where the canonizer is not used and the identity
 * of variables is not important for the final result. It can help by
 * normalizing expressions to a small degree.
 */

package za.ac.sun.cs.green.service.renamer;
