package model.beans;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.ValueSource;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;

class UtenteTest {

    private Utente user;

    @BeforeEach
    void setUp() {
        user = new Utente();
    }

    // --- Constructor ---
    // Frame F1
    @Test
    @DisplayName("F1: Initialize a new Utente object")
    void testDefaultConstructor() {
        // Act & Assert
        assertNotNull(user, "Utente object should not be null");
    }

    // --- setId / getId ---
    // Frames F1, F2, F3
    @ParameterizedTest
    @ValueSource(ints = { 1, 0, -1 })
    @DisplayName("F1, F2, F3: Set ID with positive, zero, and negative values")
    void parameterizedTestId(int id) {
        // Act
        user.setId(id);

        // Assert
        assertEquals(id, user.getId(), "getId should return the set ID");
    }

    // --- setNome / getNome ---
    // Frame F4
    @ParameterizedTest
    @ValueSource(strings = { "Mario", "Luigi", "Peach" })
    @DisplayName("F4: Set valid nome")
    void shouldSetNomeWhenValid(String validName) {
        // Act
        user.setNome(validName);

        // Assert
        assertEquals(validName, user.getNome(), "getNome should return the set nome");
    }

    // Frames F5, F6, F7
    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F5, F6, F7: Set invalid nome (null, empty, blank) throws IllegalArgumentException")
    void shouldThrowExceptionWhenNomeIsInvalid(String invalidName) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.setNome(invalidName));
        assertTrue(exception.getMessage().contains("Il nome non può essere null"));
    }

    // --- setCognome / getCognome ---
    // Frame F8
    @Test
    @DisplayName("F8: Set valid cognome")
    void shouldSetCognomeWhenValid() {
        // Arrange
        String validCognome = "Rossi";

        // Act
        user.setCognome(validCognome);

        // Assert
        assertEquals(validCognome, user.getCognome(), "getCognome should return the set cognome");
    }

    // Frames F9, F10, F11
    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F9, F10, F11: Set invalid cognome (null, empty, blank) throws IllegalArgumentException")
    void shouldThrowExceptionWhenCognomeIsInvalid(String invalidSurname) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.setCognome(invalidSurname));
        assertTrue(exception.getMessage().contains("Il cognome non può essere null"));
    }

    // --- setEmail / getEmail ---
    // Frame F12
    @Test
    @DisplayName("F12: Set valid email")
    void shouldSetEmailWhenValid() {
        // Arrange
        String validEmail = "test@example.com";

        // Act
        user.setEmail(validEmail);

        // Assert
        assertEquals(validEmail, user.getEmail(), "getEmail should return the set email");
    }

    // Frames F13, F14, F15
    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F13, F14, F15: Set invalid email (null, empty, blank) throws IllegalArgumentException")
    void shouldThrowExceptionWhenEmailIsInvalid(String invalidEmail) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.setEmail(invalidEmail));
        assertTrue(exception.getMessage().contains("L'email non può essere null"));
    }

    // --- setTelefono / getTelefono ---
    // Frame F16
    @Test
    @DisplayName("F16: Set valid telefono")
    void shouldSetTelefonoWhenValid() {
        // Arrange
        String validPhone = "1234567890";

        // Act
        user.setTelefono(validPhone);

        // Assert
        assertEquals(validPhone, user.getTelefono(), "getTelefono should return the set telefono");
    }

    // Frames F17, F18, F19
    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F17, F18, F19: Set invalid telefono (null, empty, blank) throws IllegalArgumentException")
    void shouldThrowExceptionWhenTelefonoIsInvalid(String invalidPhone) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.setTelefono(invalidPhone));
        assertTrue(exception.getMessage().contains("Il telefono non può essere null"));
    }

    // --- setImmagine / getImmagine ---
    // Frame F20
    @Test
    @DisplayName("F20: Set valid immagine path")
    void shouldSetImmagineWhenValid() {
        // Arrange
        String imagePath = "/images/profile.jpg";

        // Act
        user.setImmagine(imagePath);

        // Assert
        assertEquals(imagePath, user.getImmagine(), "getImmagine should return the set path");
    }

    // Frame F21
    @Test
    @DisplayName("F21: Set null immagine")
    void shouldSetImmagineWhenNull() {
        // Act
        user.setImmagine(null);

        // Assert
        assertNull(user.getImmagine(), "getImmagine should return null when set to null");
    }

    // --- setAdmin / isAdmin ---
    // Frames F22, F23
    @ParameterizedTest
    @ValueSource(booleans = { true, false })
    @DisplayName("F22, F23: Set admin status")
    void shouldSetAdminStatus(boolean status) {
        // Act
        user.setAdmin(status);

        // Assert
        assertEquals(status, user.isAdmin(), "isAdmin should match the set status");
    }

    // --- setOrdini / getOrdini ---
    // Frame F24
    @Test
    @DisplayName("F24: Set populated ordini list")
    void shouldSetOrdiniWhenValid() {
        // Arrange
        ArrayList<Ordine> arrayOrders = new ArrayList<>();
        Ordine order = new Ordine();
        arrayOrders.add(order);

        // Act
        user.setOrdini(arrayOrders);

        // Assert
        assertEquals(arrayOrders, user.getOrdini(), "getOrdini should return the populated list");
    }

    // Frame F25
    @Test
    @DisplayName("F25: Set empty ordini list")
    void shouldSetOrdiniWhenEmpty() {
        // Arrange
        ArrayList<Ordine> arrayOrders = new ArrayList<>();

        // Act
        user.setOrdini(arrayOrders);

        // Assert
        assertAll("getOrdini should return an empty list",
                () -> assertNotNull(user.getOrdini()),
                () -> assertTrue(user.getOrdini().isEmpty()));
    }

    // Frame F26
    @Test
    @DisplayName("F26: Set null ordini list throws IllegalArgumentException")
    void shouldThrowExceptionWhenOrdiniIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.setOrdini(null));
        assertTrue(exception.getMessage().contains("La lista degli ordini non può essere null"));
    }

    // --- setRecensioni / getRecensioni ---
    // Frame F27
    @Test
    @DisplayName("F27: Set populated recensioni list")
    void shouldSetRecensioniWhenValid() {
        // Arrange
        ArrayList<Recensione> arrayReviews = new ArrayList<>();
        Recensione review = new Recensione();
        arrayReviews.add(review);

        // Act
        user.setRecensioni(arrayReviews);

        // Assert
        assertEquals(arrayReviews, user.getRecensioni(), "getRecensioni should return the populated list");
    }

    // Frame F28
    @Test
    @DisplayName("F28: Set empty recensioni list")
    void shouldSetRecensioniWhenEmpty() {
        // Arrange
        ArrayList<Recensione> arrayReviews = new ArrayList<>();

        // Act
        user.setRecensioni(arrayReviews);

        // Assert
        assertAll("getRecensioni should return an empty list",
                () -> assertNotNull(user.getRecensioni()),
                () -> assertTrue(user.getRecensioni().isEmpty()));
    }

    // Frame F29
    @Test
    @DisplayName("F29: Set null recensioni list throws IllegalArgumentException")
    void shouldThrowExceptionWhenRecensioniIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.setRecensioni(null));
        assertTrue(exception.getMessage().contains("La lista delle recensioni non può essere null"));
    }

    // --- setPassword / getPassword ---
    // Frame F30
    @Test
    @DisplayName("F30: getPassword returns SHA-1 hash")
    void shouldReturnSha1HashFromGetPassword() throws NoSuchAlgorithmException {
        // Arrange
        String rawPassword = "secretPassword";

        // Act
        user.setPassword(rawPassword);
        String savedPassword = user.getPassword();

        // Expected Hash Calculation
        MessageDigest digest = MessageDigest.getInstance("SHA-1");
        digest.reset();
        digest.update(rawPassword.getBytes(StandardCharsets.UTF_8));
        String expectedHash = String.format("%040x", new BigInteger(1, digest.digest()));

        // Assert
        assertAll("Hash Verification",
                () -> assertNotNull(savedPassword),
                () -> assertEquals(40, savedPassword.length(), "SHA-1 hash length should be 40 characters"),
                () -> assertEquals(expectedHash, savedPassword, "Password should match the expected SHA-1 hash"));
    }

    // Frames F31, F32
    @ParameterizedTest
    @NullAndEmptySource
    @ValueSource(strings = { "   " })
    @DisplayName("F31, F32: Set invalid password (null, empty, blank) throws IllegalArgumentException")
    void shouldThrowExceptionWhenPasswordIsInvalid(String invalidPassword) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.setPassword(invalidPassword));
        assertTrue(exception.getMessage().contains("La password non può essere null"));
    }

    // --- getOrdineIndex ---
    // Frame F33
    @Test
    @DisplayName("F33: getOrdineIndex throws IllegalArgumentException when Ordine is null")
    void shouldThrowExceptionWhenOrderIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> user.getOrdineIndex(null));
        assertTrue(exception.getMessage().contains("L'ordine non può essere null"));
    }

    // Frame F34
    @Test
    @DisplayName("F34: getOrdineIndex returns -1 when Ordini list is null")
    void shouldReturnMinusOneWhenOrdiniListIsNull() {
        // Arrange
        Ordine order = new Ordine();

        // Act & Assert
        assertEquals(-1, user.getOrdineIndex(order), "Should return -1 when ordini list is null");
    }

    // Frame F35
    @Test
    @DisplayName("F35: getOrdineIndex returns -1 when Ordini list is empty")
    void shouldReturnMinusOneWhenOrdiniListIsEmpty() {
        // Arrange
        ArrayList<Ordine> emptyArrayOrders = new ArrayList<>();
        user.setOrdini(emptyArrayOrders);
        Ordine order = new Ordine();

        // Act & Assert
        assertEquals(-1, user.getOrdineIndex(order), "Should return -1 when ordini list is empty");
    }

    // Frame F36
    @Test
    @DisplayName("F36: getOrdineIndex returns correct index when Ordine exists in list")
    void shouldReturnCorrectIndexWhenOrderExists() {
        // Arrange
        Ordine order1 = createValidOrder(1);
        Ordine order2 = createValidOrder(2);
        ArrayList<Ordine> arrayOrders = new ArrayList<>();
        arrayOrders.add(order1);
        arrayOrders.add(order2);

        // Act
        user.setOrdini(arrayOrders);

        // Assert
        assertAll("getOrdineIndex should return correct index when Ordine exists in list",
                () -> assertEquals(0, user.getOrdineIndex(order1), "Should return index 0 for order with ID 1"),
                () -> assertEquals(1, user.getOrdineIndex(order2), "Should return index 1 for order with ID 2"));
    }

    // Frame F37
    @Test
    @DisplayName("F37: getOrdineIndex returns -1 when Ordine does not exist in list")
    void shouldReturnMinusOneWhenOrderNotFound() {
        // Arrange
        Ordine orderInList = createValidOrder(1);
        Ordine orderNotInList = createValidOrder(99);
        ArrayList<Ordine> arrayOrders = new ArrayList<>();
        arrayOrders.add(orderInList);

        // Act
        user.setOrdini(arrayOrders);

        // Assert
        assertEquals(-1, user.getOrdineIndex(orderNotInList), "Should return -1 when order is not found");
    }

    // Helper method
    private Ordine createValidOrder(int id) {
        Ordine order = new Ordine();
        order.setId(id);
        return order;
    }
}
