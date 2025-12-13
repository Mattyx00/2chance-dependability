package services;

import model.beans.Utente;
import model.dao.UtenteDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockedStatic;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.servlet.http.Part;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class EditProfiloServiceTest {

    @Mock
    private UtenteDAO utenteDAO;

    @Mock
    private Part part;

    @InjectMocks
    private EditProfiloService editProfiloService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("F1: Initialize with valid DAO")
    void shouldInitializeWithValidDAO() {
        // Act
        EditProfiloService service = new EditProfiloService(utenteDAO);

        // Assert
        assertNotNull(service);
    }

    @Test
    @DisplayName("F2: Initialize with null DAO")
    void shouldInitializeWithNullDAO() {
        // Act
        EditProfiloService service = new EditProfiloService(null);

        // Assert
        assertNotNull(service);
    }

    // =================================================================================================
    // editProfilo Tests
    // =================================================================================================

    @Test
    @DisplayName("F10: Successful profile text update")
    void shouldUpdateProfileTextSuccessfully() throws SQLException {
        // Arrange
        int userId = 1;
        Utente initialUser = new Utente();
        initialUser.setId(userId);

        String expectedUserName = "Mario";
        Utente updatedUser = new Utente();
        updatedUser.setId(userId);
        updatedUser.setNome(expectedUserName);

        String profileField = "nome";

        when(utenteDAO.getUtenteById(userId)).thenReturn(updatedUser);

        // Act
        Utente actualUser = editProfiloService.editProfilo(initialUser, expectedUserName, profileField);

        // Assert
        verify(utenteDAO).editProfilo(profileField, expectedUserName, userId);
        verify(utenteDAO).getUtenteById(userId);
        assertEquals(expectedUserName, actualUser.getNome());
    }

    @Test
    @DisplayName("F11: Update with empty value")
    void shouldUpdateProfileWithEmptyValue() throws SQLException {
        // Arrange
        int userId = 1;
        Utente user = new Utente();
        user.setId(userId);

        String updatedUserName = "";

        String profileField = "nome";

        // Act
        editProfiloService.editProfilo(user, updatedUserName, profileField);

        // Assert
        verify(utenteDAO).editProfilo(profileField, updatedUserName, userId);
    }

    @Test
    @DisplayName("F12: Null Utente in editProfilo")
    void shouldThrowNPEWhenUserIsNullInEditProfilo() {
        // Act & Assert
        assertThrows(
                NullPointerException.class,
                () -> editProfiloService.editProfilo(null, "val", "col"));
    }

    @ParameterizedTest
    @CsvSource({
            "nome, Mario",
            "email, test@test.com",
            "telefono, 123456"
    })
    @DisplayName("Should pass valid arguments to DAO for various inputs")
    void shouldPassArgumentsToDaoForVariousInputs(String profileField, String updatedProfileField)
            throws SQLException {
        // Arrange
        int userId = 1;
        Utente user = new Utente();
        user.setId(userId);

        // Act
        editProfiloService.editProfilo(user, updatedProfileField, profileField);

        // Assert
        verify(utenteDAO).editProfilo(profileField, updatedProfileField, userId);
    }
}
