package za.ac.sun.cs.green.parser.isl;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;

/**
 * @date: 2017/08/14
 * @author: JH Taljaard.
 * @contributor: Jaco Geldenhuys
 * Student Number: 18509193.
 *
 * Description:
 * Specific scanner for the parser
 */
public class Scanner {

    public static final int UNKNOWN = 0;
    public static final int EOF = 1;
    public static final int INTEGER = 2;
    public static final int VARIABLE = 3;

    /* TOKENS */
    public static final int AND = 4;
    public static final int ARROW = 5;
    public static final int COLON = 6;
    public static final int COMMA = 7;
    public static final int EQ = 8;
    public static final int EXP = 9;
    public static final int GE = 10;
    public static final int GT = 11;
    public static final int LBRACE = 12;
    public static final int LBRACKET = 13;
    public static final int LE = 14;
    public static final int LT = 15;
    public static final int LPAREN = 16;
    public static final int MINUS = 17;
    public static final int MUL = 18;
    public static final int PLUS = 19;
    public static final int RBRACE = 20;
    public static final int RBRACKET = 21;
    public static final int RPAREN = 22;
    public static final int SEMICOLON = 23;

    public static final int DIV = 24;
    public static final int NE = 25;
    public static final int FLOOR = 26;
    public static final int POW = 27;
    public static final int NOT = 28;

    private final Reader reader;

    private int nextCh = ' ';

    private int nextToken = UNKNOWN;

    private int nextInt = -1;

    private String nextVar = null;

    public Scanner(Reader reader) {
        this.reader = reader;
        readNextToken();
    }

    public Scanner(String input) {
        this(new StringReader(input));
    }

    private void readNextCh() {
        try {
            nextCh = reader.read();
        } catch (IOException x) {
            throw new RuntimeException("io error", x);
        }
    }

    private void readNextToken() {
        nextToken = UNKNOWN;
        while (nextToken == UNKNOWN) {
            if (nextCh == -1) {
                nextToken = EOF;
            } else if (Character.isWhitespace(nextCh)) {
                readNextCh();
            } else if (nextCh == ':') {
                nextToken = COLON;
                readNextCh();
            } else if (nextCh == ',') {
                nextToken = COMMA;
                readNextCh();
            } else if (nextCh == '=') {
                nextToken = EQ;
                readNextCh();
            } else if (nextCh == '^') {
                nextToken = POW;
                readNextCh();
            } else if (nextCh == '{') {
                nextToken = LBRACE;
                readNextCh();
            } else if (nextCh == '[') {
                nextToken = LBRACKET;
                readNextCh();
            } else if (nextCh == '(') {
                nextToken = LPAREN;
                readNextCh();
            } else if (nextCh == '*') {
                nextToken = MUL;
                readNextCh();
            } else if (nextCh == '+') {
                nextToken = PLUS;
                readNextCh();
            } else if (nextCh == '}') {
                nextToken = RBRACE;
                readNextCh();
            } else if (nextCh == ']') {
                nextToken = RBRACKET;
                readNextCh();
            } else if (nextCh == ')') {
                nextToken = RPAREN;
                readNextCh();
            } else if (nextCh == ';') {
                nextToken = SEMICOLON;
                readNextCh();
            } else if (nextCh == '/') {
                nextToken = DIV;
                readNextCh();
            } else if (nextCh == '-') {
                nextToken = MINUS;
                readNextCh();
                if (nextCh == '>') {
                    nextToken = ARROW;
                    readNextCh();
                }
            } else if (nextCh == '>') {
                nextToken = GT;
                readNextCh();
                if (nextCh == '=') {
                    nextToken = GE;
                    readNextCh();
                }
            } else if (nextCh == '<') {
                nextToken = LT;
                readNextCh();
                if (nextCh == '=') {
                    nextToken = LE;
                    readNextCh();
                }
            } else if (nextCh == '!') {
                readNextCh();
                if (nextCh == '=') {
                    nextToken = NE;
                    readNextCh();
                }
            } else if (Character.isDigit(nextCh)) {
                nextInt = 0;
                while (Character.isDigit(nextCh)) {
                    nextInt = nextInt * 10 + nextCh - '0';
                    readNextCh();
                }
                nextToken = INTEGER;
            } else if (Character.isJavaIdentifierStart(nextCh)) {
                StringBuilder s = new StringBuilder();
                while (Character.isJavaIdentifierPart(nextCh)) {
                    s.append((char) nextCh);
                    readNextCh();
                }

                if (s.toString().equals("and")) {
                    nextToken = AND;
                } else if (s.toString().equals("not")) {
                    nextToken = NOT;
                } else if (s.toString().equals("floor")) {
                    nextToken = FLOOR;
                } else {
                    nextVar = s.toString();
                    nextToken = VARIABLE;
                }
            } else {
                throw new RuntimeException("unrecognizable token");
            }
        }
    }

    public void expect(int token) {
        if (token == nextToken) {
            readNextToken();
        } else {
            throw new RuntimeException("expect " + token + " but found " + nextToken);
        }
    }

    public int expectInteger() {
        int i = nextInt;
        expect(INTEGER);
        return i;
    }

    public String expectVariable() {
        String s = nextVar;
        expect(VARIABLE);
        return s;
    }

    public int next() {
        return nextToken;
    }

}