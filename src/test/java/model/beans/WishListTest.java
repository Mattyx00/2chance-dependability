package model.beans;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

class WishListTest {

    // F1: Default initialization
    @Test
    @DisplayName("Default constructor should initialize correct state")
    void testDefaultConstructor() {
        // Arrange
        WishList wishlist = new WishList();

        // Act & Assert
        assertAll("Default State",
                () -> assertNotNull(wishlist.getUtente(), "Utente should not be null by default"),
                () -> assertNotNull(wishlist.getProdotti(), "Prodotti list should not be null"),
                () -> assertTrue(wishlist.getProdotti().isEmpty(), "Prodotti list should be empty"));
    }

    // F2: Valid utente (Parameterized Constructor)
    @Test
    @DisplayName("Parameterized constructor should set utente and initialize products")
    void shouldCreateWishListWhenUtenteIsValid() {
        // Arrange
        Utente utente = new Utente();

        // Act
        WishList wishlist = new WishList(utente);

        // Assert
        assertAll("Parameterized Constructor State",
                () -> assertEquals(utente, wishlist.getUtente(), "Utente should be set correctly"),
                () -> assertNotNull(wishlist.getProdotti(), "Prodotti list should not be null"),
                () -> assertTrue(wishlist.getProdotti().isEmpty(), "Prodotti list should be empty"));
    }

    // F3: Null utente (Parameterized Constructor)
    @Test
    @DisplayName("Parameterized constructor should throw exception when utente is null")
    void shouldThrowExceptionWhenConstructorUtenteIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new WishList(null));
        assertEquals("L'utente non può essere null", exception.getMessage());
    }

    // F4, F5, F6: Set/Get Utente
    @Test
    @DisplayName("setUtente should update utente when valid")
    void shouldSetUtenteWhenValid() {
        // Arrange
        WishList wishlist = new WishList();
        Utente utente = new Utente();

        // Act
        wishlist.setUtente(utente);

        // Assert
        assertEquals(utente, wishlist.getUtente(), "getUtente should return the set utente");
    }

    // F7: Null utente (Setter)
    @Test
    @DisplayName("setUtente should throw exception when utente is null")
    void shouldThrowExceptionWhenSetUtenteIsNull() {
        // Arrange
        WishList wishlist = new WishList();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlist.setUtente(null));
        assertEquals("L'utente non può essere null", exception.getMessage());
    }

    // F8: Get products (initial state) - Covered in testDefaultConstructor

    // F9, F10: Set populated list
    @Test
    @DisplayName("setProdotti should match the provided populated list")
    void shouldSetProdottiWhenPopulated() {
        // Arrange
        WishList wishlist = new WishList();
        ArrayList<Prodotto> arrayProducts = new ArrayList<>();
        Prodotto product1 = new Prodotto();
        Prodotto product2 = new Prodotto();
        arrayProducts.add(product1);
        arrayProducts.add(product2);

        // Act
        wishlist.setProdotti(arrayProducts);

        // Assert
        assertAll("getProdotti should return the set list",
                () -> assertEquals(arrayProducts, wishlist.getProdotti(), "getProdotti should return the set list"),
                () -> assertEquals(2, wishlist.getProdotti().size(), "List size should match"));
    }

    // F11: Set empty list
    @Test
    @DisplayName("setProdotti should accept an empty list")
    void shouldSetProdottiWhenEmpty() {
        // Arrange
        WishList wishlist = new WishList();
        ArrayList<Prodotto> emptyProductList = new ArrayList<>();

        // Act
        wishlist.setProdotti(emptyProductList);

        // Assert
        assertAll("getProdotti should return the set list",
                () -> assertEquals(emptyProductList, wishlist.getProdotti()),
                () -> assertTrue(wishlist.getProdotti().isEmpty()));
    }

    // F12: Set null list
    @Test
    @DisplayName("setProdotti should throw exception when list is null")
    void shouldThrowExceptionWhenSetProdottiIsNull() {
        // Arrange
        WishList wishlist = new WishList();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> wishlist.setProdotti(null));
        assertEquals("La lista dei prodotti non può essere null", exception.getMessage());
    }
}
